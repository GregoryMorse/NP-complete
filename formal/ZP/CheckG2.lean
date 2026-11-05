module

public import ZP.CheckG

@[expose] public section

/-! # The check phase of the GI machine (part 2): the row part, column part and edge loop -/

namespace ZP.G

open ZP

theorem gd2Skip (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gD2 P (3 :: R)) (hdR QG.gD2 (P ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gd2Mark (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gD2 P (2 :: R)) (hd QG.gD3 P (2 :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 2, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gd2Col (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gD2 P (1 :: R)) (hdR QG.gN2c (P ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gd3Mark (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hd QG.gD3 (P ++ [3]) R) (hd QG.gTR1 P (2 :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 2, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gd3Done (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hd QG.gD3 (P ++ [1]) R) (hd QG.gGL P (1 :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gd2Skips (R : List Nat) (hR : Sym4 R) : ∀ (p : Nat) (P : List Nat), Sym4 P →
    zgiLogic.Reach (hdR QG.gD2 P (List.replicate p 3 ++ R)) (hdR QG.gD2 (P ++ List.replicate p 3) R)
  | 0, P, _ => by simpa using (LTM.Reach.refl _ _)
  | p + 1, P, hP => by
    have h1 := gd2Skip P (List.replicate p 3 ++ R) hP (by simp [ALL, hR])
    have h2 := gd2Skips R hR p (P ++ [3]) (by simp [ALL, hP])
    exact (h1.of_eq (by simp [List.replicate_succ]) rfl).trans (h2.of_eq rfl (by simp [List.replicate_succ, List.append_assoc]))

/-- The test after the inner loop in the row part: another cell of `m` to mark, or `m` is done. -/
theorem gd2Row (S : List Nat) (hS : Sym4 S) (q : Nat) :
    ∀ (p : Nat) (P : List Nat), Sym4 P →
    (∀ p', p = p' + 1 → zgiLogic.Reach (hdR QG.gD2 P (List.replicate p 3 ++ (List.replicate (q + 1) 2 ++ 1 :: S)))
      (hd QG.gTR1 (P ++ List.replicate p' 3) (2 :: (List.replicate (q + 1) 2 ++ 1 :: S)))) ∧
    (∀ P0, p = 0 → P = P0 ++ [1] → zgiLogic.Reach (hdR QG.gD2 P (List.replicate (q + 1) 2 ++ 1 :: S))
      (hd QG.gGL P0 (1 :: (List.replicate (q + 1) 2 ++ 1 :: S)))) := by
  intro p P hP
  have hq : Sym4 (List.replicate (q + 1) 2 ++ 1 :: S) := by
    have : Sym4 (List.replicate (q + 1) 2) := fun a ha => by
      rw [List.eq_of_mem_replicate ha]; simp [ALL]
    simp [ALL, this, hS]
  constructor
  · intro p' hp
    subst hp
    have h1 := gd2Skips (List.replicate (q + 1) 2 ++ 1 :: S) hq (p' + 1) P hP
    have hP' : Sym4 (P ++ List.replicate (p' + 1) 3) := by
      have : Sym4 (List.replicate (p' + 1) 3) := fun a ha => by
        rw [List.eq_of_mem_replicate ha]; simp [ALL]
      simp [ALL, hP, this]
    have h2 := gd2Mark (P ++ List.replicate (p' + 1) 3) (List.replicate q 2 ++ 1 :: S) hP' (by
      have : Sym4 (List.replicate q 2) := fun a ha => by
        rw [List.eq_of_mem_replicate ha]; simp [ALL]
      simp [ALL, this, hS])
    have hP'' : Sym4 (P ++ List.replicate p' 3) := by
      have : Sym4 (List.replicate p' 3) := fun a ha => by
        rw [List.eq_of_mem_replicate ha]; simp [ALL]
      simp [ALL, hP, this]
    have h3 := gd3Mark (P ++ List.replicate p' 3) (2 :: (List.replicate q 2 ++ 1 :: S)) hP'' (by
      have : Sym4 (List.replicate q 2) := fun a ha => by
        rw [List.eq_of_mem_replicate ha]; simp [ALL]
      simp [ALL, this, hS])
    have e : P ++ List.replicate (p' + 1) 3 = P ++ List.replicate p' 3 ++ [3] := by
      simp [List.replicate_succ', List.append_assoc]
    rw [e] at h1 h2
    exact h1.trans (h2.trans h3)
  · intro P0 hp hP0
    subst hp; subst hP0
    have hP0s : Sym4 P0 := fun a ha => hP a (by simp [ha])
    have h2 := gd2Mark (P0 ++ [1]) (List.replicate q 2 ++ 1 :: S) hP (by
      have : Sym4 (List.replicate q 2) := fun a ha => by
        rw [List.eq_of_mem_replicate ha]; simp [ALL]
      simp [ALL, this, hS])
    have h3 := gd3Done P0 (2 :: (List.replicate q 2 ++ 1 :: S)) hP0s (by
      have : Sym4 (List.replicate q 2) := fun a ha => by
        rw [List.eq_of_mem_replicate ha]; simp [ALL]
      simp [ALL, this, hS])
    exact h2.trans h3

end ZP.G
