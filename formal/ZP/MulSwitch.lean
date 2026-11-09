module

public import ZP.MulInterp

@[expose] public section

/-! The switch of `native/zmul.py` as Lean lemmas, over `zmulLogic`. -/

namespace ZP.Mul

open ZP

/-- The insert state that carries the symbol `y` (`'0'` = 2, `'1'` = 3, `M` = 1). -/
def mQof (y : Nat) : Nat := if y = 1 then QMul.mQM else if y = 2 then QMul.mQ0 else QMul.mQ1

def ssets : Env := [ALL, NB]

theorem svalid {A Z : List Nat} (hA : Sym4 A) (hZ : NoB Z) : Valid ssets [A, Z] :=
  Valid.cons hA (Valid.cons hZ (Valid.nil _))

theorem qsBase (y : Nat) (hy : y ∈ NB) (A0 Z : List Nat) (hA : Sym4 A0) (hZ : NoB Z) :
    zmulLogic.Reach (hdR (mQof y) (A0 ++ 0 :: Z) []) (hdR QMul.mRX (A0 ++ [0]) (Z ++ [y])) := by
  have hv := svalid hA hZ
  have hy' : y = 1 ∨ y = 2 ∨ y = 3 := by simpa [NB] using hy
  rcases hy' with rfl | rfl | rfl
  · exact checkFF (env := [A0, Z]) (E := []) (k := 8) hv trivial
      (ls := [.blk 0 .id, .sym 0, .blk 1 .id]) (rs := [])
      (ls' := [.blk 0 .id, .sym 0]) (rs' := [.blk 1 .id, .sym 1])
      (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkFF (env := [A0, Z]) (E := []) (k := 8) hv trivial
      (ls := [.blk 0 .id, .sym 0, .blk 1 .id]) (rs := [])
      (ls' := [.blk 0 .id, .sym 0]) (rs' := [.blk 1 .id, .sym 2])
      (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkFF (env := [A0, Z]) (E := []) (k := 8) hv trivial
      (ls := [.blk 0 .id, .sym 0, .blk 1 .id]) (rs := [])
      (ls' := [.blk 0 .id, .sym 0]) (rs' := [.blk 1 .id, .sym 3])
      (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)


theorem qsStep (y c : Nat) (hy : y ∈ NB) (hc : c ∈ NB) (A0 Z ST : List Nat) (hA : Sym4 A0)
    (hZ : NoB Z) (hS : NoB ST) :
    zmulLogic.Reach (hdR (mQof y) (A0 ++ 0 :: Z) (c :: ST))
      (hdR (mQof c) (A0 ++ 0 :: (Z ++ [y])) ST) := by
  have hv : Valid [ALL, NB, NB] [A0, Z, ST] :=
    Valid.cons hA (Valid.cons hZ (Valid.cons hS (Valid.nil _)))
  have hy' : y = 1 ∨ y = 2 ∨ y = 3 := by simpa [NB] using hy
  have hc' : c = 1 ∨ c = 2 ∨ c = 3 := by simpa [NB] using hc
  rcases hy' with rfl | rfl | rfl <;> rcases hc' with rfl | rfl | rfl <;>
  first
    | exact checkFF (env := [A0, Z, ST]) (E := []) (k := 6) hv trivial
        (ls := [.blk 0 .id, .sym 0, .blk 1 .id]) (rs := [.sym 1, .blk 2 .id])
        (ls' := [.blk 0 .id, .sym 0, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
    | exact checkFF (env := [A0, Z, ST]) (E := []) (k := 6) hv trivial
        (ls := [.blk 0 .id, .sym 0, .blk 1 .id]) (rs := [.sym 2, .blk 2 .id])
        (ls' := [.blk 0 .id, .sym 0, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
    | exact checkFF (env := [A0, Z, ST]) (E := []) (k := 6) hv trivial
        (ls := [.blk 0 .id, .sym 0, .blk 1 .id]) (rs := [.sym 3, .blk 2 .id])
        (ls' := [.blk 0 .id, .sym 0, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
    | exact checkFF (env := [A0, Z, ST]) (E := []) (k := 6) hv trivial
        (ls := [.blk 0 .id, .sym 0, .blk 1 .id]) (rs := [.sym 1, .blk 2 .id])
        (ls' := [.blk 0 .id, .sym 0, .blk 1 .id, .sym 2]) (rs' := [.blk 2 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
    | exact checkFF (env := [A0, Z, ST]) (E := []) (k := 6) hv trivial
        (ls := [.blk 0 .id, .sym 0, .blk 1 .id]) (rs := [.sym 2, .blk 2 .id])
        (ls' := [.blk 0 .id, .sym 0, .blk 1 .id, .sym 2]) (rs' := [.blk 2 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
    | exact checkFF (env := [A0, Z, ST]) (E := []) (k := 6) hv trivial
        (ls := [.blk 0 .id, .sym 0, .blk 1 .id]) (rs := [.sym 3, .blk 2 .id])
        (ls' := [.blk 0 .id, .sym 0, .blk 1 .id, .sym 2]) (rs' := [.blk 2 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
    | exact checkFF (env := [A0, Z, ST]) (E := []) (k := 6) hv trivial
        (ls := [.blk 0 .id, .sym 0, .blk 1 .id]) (rs := [.sym 1, .blk 2 .id])
        (ls' := [.blk 0 .id, .sym 0, .blk 1 .id, .sym 3]) (rs' := [.blk 2 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
    | exact checkFF (env := [A0, Z, ST]) (E := []) (k := 6) hv trivial
        (ls := [.blk 0 .id, .sym 0, .blk 1 .id]) (rs := [.sym 2, .blk 2 .id])
        (ls' := [.blk 0 .id, .sym 0, .blk 1 .id, .sym 3]) (rs' := [.blk 2 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
    | exact checkFF (env := [A0, Z, ST]) (E := []) (k := 6) hv trivial
        (ls := [.blk 0 .id, .sym 0, .blk 1 .id]) (rs := [.sym 3, .blk 2 .id])
        (ls' := [.blk 0 .id, .sym 0, .blk 1 .id, .sym 3]) (rs' := [.blk 2 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)

/-- Insert `y` at the front of the storage text `ST`; the head comes back to the front. -/
theorem qs (ST : List Nat) (hS : NoB ST) : ∀ (y : Nat), y ∈ NB → ∀ (A0 Z : List Nat),
    Sym4 A0 → NoB Z →
    zmulLogic.Reach (hdR (mQof y) (A0 ++ 0 :: Z) ST) (hdR QMul.mRX (A0 ++ [0]) (Z ++ y :: ST)) := by
  induction ST with
  | nil =>
    intro y hy A0 Z hA hZ
    exact qsBase y hy A0 Z hA hZ
  | cons c ST ih =>
    intro y hy A0 Z hA hZ
    have hc : c ∈ NB := hS c (List.mem_cons_self ..)
    have hS' : NoB ST := fun a ha => hS a (List.mem_cons_of_mem _ ha)
    have h1 := qsStep y c hy hc A0 Z ST hA hZ hS'
    have h2 := ih hS' c hc A0 (Z ++ [y]) hA (hZ.app (fun a ha => by
      rw [List.mem_singleton.mp ha]; exact hy))
    rw [List.append_assoc] at h2
    exact h1.trans h2

end ZP.Mul
