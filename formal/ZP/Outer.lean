module

public import ZP.AllDefs
public import ZP.Logic
public import ZP.LogicBase
public import ZP.ExtChecks
public import ZP.SymExec

@[expose] public section

/-!
# Layer N3: the outer loop of `zpBase`, segment by segment

Configurations are symbolic (`ZP/SymExec.lean`). Word variables hold logical
symbols; `bits = [2, 3]` are the symbols `'0'`, `'1'`. The segment checks are
closed by `decide +kernel`; `formal/scripts/symexec.py` mirrors the executor and
finds the fuel.
-/

namespace ZP

/-- Bits as logical symbols: `'0' = 2`, `'1' = 3`. -/
def bitsOf (w : List Bool) : List Nat := w.map fun b => if b then 3 else 2

/-- `M_g J M_1 s`. -/
def layWord (J S : Nat) : List Nat := 1 :: (bitsOf (str J) ++ 1 :: bitsOf (str S))

/-- The configuration at the start of pair `(J, S)`. -/
def lay (J S : Nat) : ZC := ⟨Q.GRB, sapp (layWord J S).reverse blank, blank⟩

def bits : List Nat := [2, 3]

theorem bitsOf_bits (w : List Bool) : ∀ a ∈ bitsOf w, a ∈ bits := by
  intro a ha
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
  cases b <;> simp [bits]

theorem mem_bits {b : Nat} (h : b ∈ bits) : b = 2 ∨ b = 3 := by
  simpa [bits] using h

theorem nil_valid (S : List Nat) : ∀ a ∈ ([] : List Nat), a ∈ S := fun _ h => by cases h

/-! ## Pair start: `M_g J M_1 s`, state `GRB` on the blank after `s` -/

def L0 : SC := ⟨Q.GRB, [.blk 1 .id, .sym 1, .blk 0 .id, .sym 1], [], false⟩

theorem lay_den (J S : Nat) : lay J S = L0.den [bitsOf (str J), bitsOf (str S)] := by
  show (⟨Q.GRB, sapp (layWord J S).reverse blank, blank⟩ : ZC) =
    ⟨Q.GRB, sapp (((bitsOf (str S)).map Fn.id.app).reverse ++ ([1].reverse ++
      (((bitsOf (str J)).map Fn.id.app).reverse ++ ([1].reverse ++ [])))) blank, blank⟩
  rw [map_id_app, map_id_app]
  simp [layWord]

/-! ## C build: `BLK` appends `M 1^(|s|+1)`, which becomes `M_2 C`, then `M_3` -/

/-- The `COPY` loop of the first `BLK`; variables `J`, `u`, `v` with `s = u ++ v`. -/
def F1 : SC := ⟨Q.COPY, [.blk 1 .id, .sym 1, .blk 0 .id, .sym 1],
  [.blk 2 .id, .sym 1, .blk 1 (.const 3)], false⟩

/-- `M_g J M_1 s M_2 C M_3` with `C = 1^(|s|+1)`, state `GRB` after `M_3`. -/
def P1 : SC := ⟨Q.GRB, [.sym 1, .sym 3, .blk 1 (.const 3), .sym 1, .blk 1 .id, .sym 1,
  .blk 0 .id, .sym 1], [], false⟩

theorem phase1 (j s : List Nat) (hj : ∀ a ∈ j, a ∈ bits) (hs : ∀ a ∈ s, a ∈ bits) :
    zpLogic.Reach1 (L0.den [j, s]) (P1.den [j, s]) := by
  have hA : zpBase.Reach1 (L0.den [j, s]) (F1.den [j, [], s]) :=
    check1 (sets := [bits, bits]) (E := []) (ρ := [[0], [], [1]]) (k := 9)
      (Valid.cons hj (Valid.cons hs (Valid.nil _))) trivial (by decide +kernel)
  have hL : zpBase.Reach (F1.den [j, [], s]) (F1.den [j, [] ++ s, []]) := by
    refine LTM.Reach.fold (S := bits) (fun u v => F1.den [j, u, v]) ?_ s [] (nil_valid _) hs
    intro u b v hb hu hv
    have hval : Valid [bits, bits, bits] [j, u, v] :=
      Valid.cons hj (Valid.cons hu (Valid.cons hv (Valid.nil _)))
    rcases mem_bits hb with rfl | rfl
    · exact body (E := []) (i := 2) (i' := 1) (k := 9) hval trivial
        (by show 2 < 3; decide) (by show 1 < 3; decide) (by decide +kernel)
    · exact body (E := []) (i := 2) (i' := 1) (k := 9) hval trivial
        (by show 2 < 3; decide) (by show 1 < 3; decide) (by decide +kernel)
  have hB : zpLogic.Reach (F1.den [j, s, []]) (P1.den [j, s]) :=
    check (sets := [bits, bits, bits]) (E := [2]) (ρ := [[0], [1]]) (k := 19)
      (Valid.cons hj (Valid.cons hs (Valid.cons (nil_valid _) (Valid.nil _)))) ⟨rfl, trivial⟩
      (by decide +kernel)
  exact ((zpBase_ext_zpLogic.reach1 (hA.trans hL))).trans hB

end ZP
