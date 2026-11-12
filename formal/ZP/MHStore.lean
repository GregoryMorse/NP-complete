module

public import ZP.MHActSeg

@[expose] public section

/-!
# Multihead storage (shared by `Z_LP` and `Z_LNL`)

The machine tape of a multihead run is

    Q  0^g  0  c  H  Y  0  S            Y = `M_g ... end of the fuel` (no blank), S = the storage

where `c` holds the symbol under the current head (blank at the end markers) and `S` is the storage:
one *unit* per head, head `|P|` leftmost, head `0` rightmost. With `u = x ++ [0]` (the input cells
and the final `0`, as machine symbols `2`/`3`), the unit of a head at position `p` (`0 ≤ p ≤ |x|+1`) is

    uc u p mk  =  M :: (u.take p ++ mk :: u.drop p)

and `mk` is the marker: `0` (blank) for the current head, `1` (`M`) for the others. The cell left of
the marker is the scanned cell: the unit's `M` for `p = 0`, the cell `u[p-1]` otherwise; `p = |x|+1`
is the cell after the input (`none`).

`storeOf x pos cur` is the storage for the head positions `pos` (head `i` at `pos[i]`) and the
current head `cur`. It is `cfg u SL q SR` with `SL` the units of the heads above `cur`, `q` the position
of the current head and `SR` the units of the heads below.
-/

namespace ZP

theorem LTM.Reach.ofEq {M : LTM} {c1 c2 c3 c4 : ZC} (h : M.Reach c1 c2) (e1 : c1 = c3) (e2 : c2 = c4) :
    M.Reach c3 c4 := e1 ▸ e2 ▸ h

end ZP

namespace ZP.MH

open ZP

theorem hd_eq {q : Nat} {A A' R R' : List Nat} (h1 : A = A') (h2 : R = R') : hd q A R = hd q A' R' := by
  rw [h1, h2]

theorem hdR_eq {q : Nat} {A A' R R' : List Nat} (h1 : A = A') (h2 : R = R') :
    hdR q A R = hdR q A' R' := by
  rw [h1, h2]

theorem NoB.cons {b : Nat} {w : List Nat} (hb : b ∈ NB) (hw : NoB w) : NoB (b :: w) := by
  intro a ha
  rcases List.mem_cons.mp ha with e | e
  · rw [e]; exact hb
  · exact hw a e

/-- The machine symbol of a bit. -/
def bn (b : Bool) : Nat := if b then 3 else 2

theorem bn_bits (b : Bool) : bn b ∈ bits := by cases b <;> simp [bn, bits]

theorem bn_cases (b : Bool) : bn b = 0 ∨ bn b = 2 ∨ bn b = 3 := by cases b <;> simp [bn]

/-- The cell for the scanned symbol (`none` is the blank). -/
def cellN : Option Bool → Nat
  | none => 0
  | some false => 2
  | some true => 3

theorem cellN_some (b : Bool) : cellN (some b) = bn b := by cases b <;> rfl

/-- The input cells followed by the final `0` cell. -/
def uOf (x : List Bool) : List Nat := bitsOf x ++ [2]

theorem Bits.uOf (x : List Bool) : Bits (uOf x) := by
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact Bits.ofB x a h
  · simp at h
    subst h
    simp [bits]

theorem length_uOf (x : List Bool) : (uOf x).length = x.length + 1 := by
  simp [uOf, bitsOf]

/-- A unit: `M`, the cells `u`, with the marker `mk` after the first `p` of them. -/
def uc (u : List Nat) (p mk : Nat) : List Nat := 1 :: (u.take p ++ mk :: u.drop p)

/-- The units of the heads at positions `ps` (listed from head 0 up), head 0 rightmost, all unmarked. -/
def ucs (u : List Nat) (ps : List Nat) : List Nat := ps.reverse.flatMap fun p => uc u p 1

@[simp] theorem ucs_nil (u : List Nat) : ucs u [] = [] := rfl

theorem ucs_cons (u : List Nat) (p : Nat) (ps : List Nat) : ucs u (p :: ps) = ucs u ps ++ uc u p 1 := by
  simp [ucs]

theorem ucs_snoc (u : List Nat) (ps : List Nat) (p : Nat) : ucs u (ps ++ [p]) = uc u p 1 ++ ucs u ps := by
  simp [ucs]

/-- The storage with the units `SL` left, the current unit at position `q`, the units `SR` right. -/
def cfg (u : List Nat) (SL : List Nat) (q : Nat) (SR : List Nat) : List Nat := SL ++ uc u q 0 ++ SR

/-- The storage of a multihead run. -/
def storeOf (x : List Bool) (pos : List Nat) (cur : Nat) : List Nat :=
  cfg (uOf x) (ucs (uOf x) (pos.drop (cur + 1))) (pos.getD cur 0) (ucs (uOf x) (pos.take cur))

/-- The cell read from the scanned cell: the blank at the unit's `M` and at the final cell. -/
def rdCell (u : List Nat) (q : Nat) : Nat := if q = 0 ∨ q = u.length then 0 else u.getD (q - 1) 0

theorem cellN_mhRead (x : List Bool) (p : Nat) (hp : p ≤ x.length + 1) :
    cellN (mhRead x p) = rdCell (uOf x) p := by
  unfold mhRead rdCell
  rw [length_uOf]
  by_cases h : p = 0 ∨ p = x.length + 1
  · simp [h, cellN]
  · have h1 : 1 ≤ p := by omega
    have h2 : p - 1 < x.length := by omega
    simp only [h, ite_false]
    rw [List.getElem?_eq_getElem h2]
    simp only [uOf, bitsOf, List.getD]
    rw [List.getElem?_append_left (by simpa using h2)]
    simp [List.getElem?_map, List.getElem?_eq_getElem h2]
    cases x[p - 1] <;> simp [bn, cellN]

theorem NoB.uc {u : List Nat} (hu : Bits u) (p : Nat) : NoB (uc u p 1) := by
  intro a ha
  simp only [ZP.MH.uc, List.mem_cons, List.mem_append] at ha
  rcases ha with rfl | (h | rfl | h)
  · simp [NB]
  · have := hu a (List.mem_of_mem_take h)
    simp [bits] at this
    simp [NB]; omega
  · simp [NB]
  · have := hu a (List.mem_of_mem_drop h)
    simp [bits] at this
    simp [NB]; omega

theorem NoB.ucs {u : List Nat} (hu : Bits u) (ps : List Nat) : NoB (ucs u ps) := by
  intro a ha
  simp only [ZP.MH.ucs, List.mem_flatMap] at ha
  obtain ⟨p, -, hp⟩ := ha
  exact NoB.uc hu p a hp

/-- The units to the right of the current one are empty or start with `M`. -/
theorem ucs_shape (u : List Nat) (ps : List Nat) : ucs u ps = [] ∨ ∃ S, ucs u ps = 1 :: S := by
  rcases List.eq_nil_or_concat ps with rfl | ⟨ps', p, rfl⟩
  · exact Or.inl rfl
  · rw [List.concat_eq_append]
    refine Or.inr ⟨(u.take p ++ 1 :: u.drop p) ++ ucs u ps', ?_⟩
    rw [ucs_snoc]
    simp [uc]


theorem cellN_cases (c : Option Bool) : cellN c = 0 ∨ cellN c = 2 ∨ cellN c = 3 := by
  rcases c with _ | _ | _ <;> simp [cellN]

theorem Sym4.uc {u : List Nat} (hu : Bits u) (p mk : Nat) (hmk : mk ∈ ALL) : Sym4 (uc u p mk) := by
  intro a ha
  simp only [ZP.MH.uc, List.mem_cons, List.mem_append] at ha
  rcases ha with rfl | (h | rfl | h)
  · simp [ALL]
  · exact hu.sym4 a (List.mem_of_mem_take h)
  · exact hmk
  · exact hu.sym4 a (List.mem_of_mem_drop h)

theorem sym4_storeOf (x : List Bool) (pos : List Nat) (cur : Nat) : Sym4 (storeOf x pos cur) := by
  have hu := Bits.uOf x
  unfold storeOf cfg
  exact ((NoB.ucs hu _).sym4.app (Sym4.uc hu _ 0 (by simp [ALL]))).app (NoB.ucs hu _).sym4

end ZP.MH
