module

@[expose] public section

/-!
# Definitions for the NTT machine (`native/zntt.py`, `ref/zntt_ref.py`)

`evalC n p recs` mirrors `zntt_ref.evaluate` literally. The prime `p` is a parameter here;
the prime function `primeN` is introduced separately.
-/

namespace ZP

/-- A record: pointer `u` (`none` or an earlier index) and coefficient `b`. -/
abbrev Rec := Option Nat × Nat

/-- The contribution of a pointer. -/
def ptrVal (u : Option Nat) (j b : Nat) (vs : List Nat) : Nat :=
  match u with
  | some u => if u < j then b * vs.getD u 0 else 0
  | none => 0

/-- Node values of pass `t`: `valsAux t p j recs vs` appends the values of `recs` (starting at
index `j`) to `vs`. -/
def valsAux (t p : Nat) : Nat → List Rec → List Nat → List Nat
  | _, [], vs => vs
  | j, (u, b) :: rs, vs =>
    let v := ((if j = t then 1 else 0) + vs.getLastD 0 + ptrVal u j b vs) % p
    valsAux t p (j + 1) rs (vs ++ [v])

/-- One pass `t`: compare outputs with `E`, update `E`, check the power sum. -/
def evalPass (n p : Nat) (recs : List Rec) (t : Nat) (E : List Nat) : Option (List Nat) :=
  let N := recs.length
  let zs := (recs.drop (N - n)).map Prod.snd
  let val := valsAux t p 0 recs []
  if (List.range n).all (fun k => val.getD (N - n + k) 0 == E.getD k 0) then
    let E' := (List.range n).map fun k => E.getD k 0 * zs.getD k 0 % p
    if ((E'.foldl (· + ·) 0 % p == 0) == (t == n - 1)) then none else some E'
  else none

def evalC (n p : Nat) (recs : List Rec) : Bool :=
  ((List.range n).foldl (fun st t => st.bind fun E => evalPass n p recs t E) (some (List.replicate n 1))).isSome

end ZP
