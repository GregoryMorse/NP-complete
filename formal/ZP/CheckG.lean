module

public import ZP.SearchG

@[expose] public section

/-! # The check phase of the GI machine: unmarking walk over the stack and `m` -/

namespace ZP.G

open ZP

theorem gglStart (X : List Nat) (a : Nat) (ha : a ∈ NB) (hX : Sym4 X) :
    zgiLogic.Reach (hdR QG.gGL [0] (a :: X)) (hdR QG.gUW2 [0] (a :: X)) := by
  have hV : Valid [ALL] [X] := Valid.cons hX (Valid.nil _)
  simp [NB] at ha
  rcases ha with rfl | rfl | rfl
  · exact checkFF (env := [X]) (E := []) (k := 4) hV trivial
      (ls := [.sym 0]) (rs := [.sym 1, .blk 0 .id]) (ls' := [.sym 0]) (rs' := [.sym 1, .blk 0 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [X]) (E := []) (k := 4) hV trivial
      (ls := [.sym 0]) (rs := [.sym 2, .blk 0 .id]) (ls' := [.sym 0]) (rs' := [.sym 2, .blk 0 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [X]) (E := []) (k := 4) hV trivial
      (ls := [.sym 0]) (rs := [.sym 3, .blk 0 .id]) (ls' := [.sym 0]) (rs' := [.sym 3, .blk 0 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gglWalk (A R : List Nat) (hA : NoB A) (hR : Sym4 R) :
    zgiLogic.Reach (hd QG.gGL A R) (hdR QG.gUW2 [0] (A ++ R)) := by
  have hV : Valid [NB, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id]) (ls' := [.sym 0]) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem uwStep (q q' : Nat) (P R : List Nat) (b : Nat) (hb : b ∈ bits) (hP : Sym4 P) (hR : Sym4 R)
    (hq : q = QG.gUW ∨ q = QG.gUW2) (hq' : q' = QG.gUW) :
    zgiLogic.Reach (hdR q P (b :: R)) (hdR q' (P ++ [unm1 b]) R) := by
  subst hq'
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  rcases mem_bits hb with rfl | rfl <;> rcases hq with rfl | rfl
  · exact (checkFF (env := [P, R]) (E := []) (k := 3) (q' := QG.gUW) (A' := P ++ [3]) (R' := R) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)).of_eq rfl (by simp [unm1])
  · exact (checkFF (env := [P, R]) (E := []) (k := 3) (q' := QG.gUW) (A' := P ++ [3]) (R' := R) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)).of_eq rfl (by simp [unm1])
  · exact (checkFF (env := [P, R]) (E := []) (k := 3) (q' := QG.gUW) (A' := P ++ [3]) (R' := R) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)).of_eq rfl (by simp [unm1])
  · exact (checkFF (env := [P, R]) (E := []) (k := 3) (q' := QG.gUW) (A' := P ++ [3]) (R' := R) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)).of_eq rfl (by simp [unm1])

theorem uwEnd (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gUW P (1 :: R)) (hdR QG.gUW2 (P ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem uwCells (R : List Nat) (hR : Sym4 R) : ∀ (c P : List Nat), Bits c → Sym4 P →
    zgiLogic.Reach (hdR QG.gUW P (c ++ 1 :: R)) (hdR QG.gUW2 (P ++ unm c ++ [1]) R)
  | [], P, _, hP => (uwEnd P R hP hR).of_eq (by simp) (by simp)
  | b :: c, P, hc, hP => by
    have hb := hc b (List.mem_cons_self ..)
    have hc' : Bits c := fun a ha => hc a (List.mem_cons_of_mem _ ha)
    have h1 := uwStep QG.gUW QG.gUW P (c ++ 1 :: R) b hb hP (by simp [ALL, hR, hc'.sym4]) (Or.inl rfl) rfl
    have hP' : Sym4 (P ++ [unm1 b]) := by
      rcases mem_bits hb with rfl | rfl <;> simp [unm1, ALL, hP]
    have h2 := uwCells R hR c (P ++ [unm1 b]) hc' hP'
    exact (h1.of_eq rfl rfl).trans (h2.of_eq rfl (by simp [unm]))

end ZP.G
