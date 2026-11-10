module

public import ZP.DefsF
public import ZP.TableG
public import ZP.DefsD

@[expose] public section

/-!
# Definitions for the GI machine (`native/zgi.py`, `ref/zgi_ref.py`)

Instance (unary): split `s` at its `0`s into runs of `1`s and read the run lengths last to
first: `T = [m, X…, 0, H…, 0, …]`. `X` is an edge list of labels, `H` a flattened `m`-column
adjacency matrix (entries `≥ 2` are edges). `s ∈ L_GI` iff some injective `w : {1..t} → {1..m}`
maps the edges of `X` one-to-one onto the edges of `H`.
-/

namespace ZP

/-- Run lengths of `s` split at `false`, in order. -/
def runsAux : List Bool → Nat → List Nat
  | [], c => [c]
  | true :: r, c => runsAux r (c + 1)
  | false :: r, c => c :: runsAux r 0

/-- `ref/zgi_ref.parse`: `(m, X, H)`. -/
def parseG (s : List Bool) : Nat × List Nat × List Nat :=
  let T := (runsAux s 0).reverse
  let m := T.headD 0
  let rest := T.tail
  let X := rest.takeWhile (· != 0)
  let rest2 := rest.drop (X.length + 1)
  let H := rest2.takeWhile (· != 0)
  (m, X, H)

/-- Pairs of consecutive entries. -/
def pairsOf : List Nat → List (Nat × Nat)
  | x :: y :: r => (x, y) :: pairsOf r
  | _ => []

/-- `ref/zgi_ref.check`: scan the edges of `X`, collecting the used entries `k` of `H`. -/
def checkEdges (w : List Nat) (m : Nat) (H : List Nat) :
    List (Nat × Nat) → List Nat → Option (List Nat)
  | [], used => some used
  | (x, y) :: r, used =>
    if x > w.length ∨ y > w.length then none else
    let k := (w.getD (x - 1) 0 - 1) * m + w.getD (y - 1) 0
    if k > H.length ∨ H.getD (k - 1) 0 < 2 ∨ k ∈ used then none
    else checkEdges w m H r (k :: used)

def checkG (w : List Nat) (m : Nat) (X H : List Nat) : Bool :=
  decide (X.length % 2 = 0) &&
  match checkEdges w m H (pairsOf X) [] with
  | none => false
  | some used => (List.range H.length).all fun k => decide (H.getD k 0 < 2) || decide (k + 1 ∈ used)

/-- All injective lists of length `t` with entries in `1..m`. -/
def injL (m : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | t + 1 => (injL m t).flatMap fun w =>
    ((List.range m).map (· + 1)).filterMap fun v => if v ∈ w then none else some (w ++ [v])

def inLG (s : List Bool) : Bool :=
  let r := parseG s
  (List.range (r.1 + 1)).any fun t => (injL r.1 t).any fun w => checkG w r.1 r.2.1 r.2.2

def CorrectG (J S : Nat) : Prop :=
  run (str J) (str S) (clock (str J) (str S)) = inLG (str S)

instance (J S : Nat) : Decidable (CorrectG J S) :=
  inferInstanceAs (Decidable (run (str J) (str S) (clock (str J) (str S)) = inLG (str S)))

def SentenceG : Prop := ∃ J, 1 ≤ J ∧ ∀ S, 1 ≤ S → CorrectG J S

end ZP
