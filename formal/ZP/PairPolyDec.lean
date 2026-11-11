module

public import ZP.PairPolyCharge

@[expose] public section

/-!
# The decider phase of one pair

From `TR` the walker goes through `K` and builds `|K| + 1` blocks of decider fuel, then the
charge of `|a|` and the guest run of `a` on `s` with the remaining fuel.
-/

namespace ZP.Poly

open ZP

/-- `GRB` walks right over non-blank cells. -/
theorem grbWalk (L X R : List Nat) (hL : Sym4 L) (hX : NoB X) (hR : Sym4 R) :
    zppolyLogic.Reach (hdR Q.GRB L (X ++ R)) (hdR Q.GRB (L ++ X) R) := by
  have hv : Valid wsets [L, X, R] := Valid.cons hL (Valid.cons hX (Valid.cons hR (Valid.nil _)))
  exact checkFF (env := [L, X, R]) (E := []) (k := 3) hv trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem blkCopyP (Kl Kr a s T : List Nat) (hKl : Bits Kl) (hKr : Bits Kr) (ha : Bits a)
    (hs : Bits s) (hT : ∀ x ∈ T, x ∈ O13) :
    zppolyLogic.Reach (hdR Q.GRB (Kl ++ 1 :: (Kr ++ 1 :: (a ++ 1 :: (s ++ 1 :: T)))) [])
      (hdR Q.COPY (Kl ++ 1 :: (Kr ++ 1 :: (a ++ 1 :: s))) (1 :: (T ++ 1 :: List.replicate s.length 3))) := by
  have hP : NoB (Kl ++ 1 :: (Kr ++ 1 :: (a ++ [1]))) :=
    hKl.noB.app (NoB.cons one_nb (hKr.noB.app (NoB.cons one_nb (ha.noB.app (NoB.cons one_nb NoB.nil)))))
  exact (blkStart Kl Kr a s T hKl hKr ha hs hT).trans
    ((copyLoop _ T hP hT s [] Bits.nil hs).of_eq (by simp) (by simp))

/-- The decider fuel: one block per position of the walker. -/
theorem decFuelP (a s t : List Nat) (ha : Bits a) (n : Nat) (hn : s.length = n) (hs : Bits s)
    (ht : ∀ x ∈ t, x ∈ T3) :
    ∀ Kr Kl i, Bits Kl → Bits Kr →
      zppolyLogic.Reach
        (hdR Q.GRB (Kl ++ 1 :: (Kr ++ 1 :: (a ++ 1 :: (s ++ 1 :: 1 :: (t ++ 1 :: FWr n (List.replicate i (n + 1))))))) [])
        (hdR QPoly.CHS [1] (1 :: (Kl ++ Kr ++ 1 :: (a ++ 1 :: (s ++ 1 :: 1 :: (t ++ 1 ::
          FWr n (List.replicate (i + Kr.length + 1) (n + 1)))))))) := by
  intro Kr
  induction Kr with
  | nil =>
    intro Kl i hKl _
    have hBl := FWr_full_o13 n i
    have hT : ∀ x ∈ 1 :: (t ++ 1 :: FWr n (List.replicate i (n + 1))), x ∈ O13 := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [O13]
      rcases List.mem_append.mp hx with h | h
      · have := ht x h; simp [T3] at this; subst this; simp [O13]
      rcases List.mem_cons.mp h with rfl | h
      · simp [O13]
      · exact hBl x h
    have eF : FWr n (List.replicate (i + ([] : List Nat).length + 1) (n + 1)) =
        FWr n (List.replicate i (n + 1)) ++ (1 :: (List.replicate s.length 3 ++ [3])) := by
      show FWr n (List.replicate i (n + 1)) ++ blkW n (n + 1) = _
      rw [blkW_full, hn, rep_snoc_eq, List.replicate_succ]
    have hA := blkCopyP Kl [] a s _ hKl Bits.nil ha hs hT
    have hL := blkDecLast Kl a s t (FWr n (List.replicate i (n + 1))) hKl ha hs ht hBl
    have hY : NoB (1 :: (a ++ 1 :: (s ++ 1 :: 1 :: (t ++ 1 :: (FWr n (List.replicate i (n + 1)) ++
        1 :: (List.replicate s.length 3 ++ [3])))))) :=
      NoB.cons one_nb (ha.noB.app (NoB.cons one_nb (hs.noB.app (NoB.cons one_nb (NoB.cons one_nb
        ((t3_noB ht).app (NoB.cons one_nb ((o13_noB hBl).app (NoB.cons one_nb
        ((t3_noB (rep_t3 _)).app (NoB.cons (by simp [NB]) NoB.nil)))))))))))
    have hW := wbLoop Kl.reverse _ hKl.rev hY.sym4
    have hE := wbEnd Kl (a ++ 1 :: (s ++ 1 :: 1 :: (t ++ 1 :: (FWr n (List.replicate i (n + 1)) ++
        1 :: (List.replicate s.length 3 ++ [3]))))) hKl (by
          have := hY.sym4
          intro x hx; exact this x (List.mem_cons_of_mem _ hx))
    refine (hA.trans ((hL.of_eq (by simp) rfl).trans ((hW.of_eq (by simp) (by simp)).trans
      (hE.of_eq rfl rfl)))).of_eq rfl ?_
    rw [eF]
    simp
  | cons b Kr' ih =>
    intro Kl i hKl hKr
    have hBl := FWr_full_o13 n i
    have hT : ∀ x ∈ 1 :: (t ++ 1 :: FWr n (List.replicate i (n + 1))), x ∈ O13 := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [O13]
      rcases List.mem_append.mp hx with h | h
      · have := ht x h; simp [T3] at this; subst this; simp [O13]
      rcases List.mem_cons.mp h with rfl | h
      · simp [O13]
      · exact hBl x h
    have eF : FWr n (List.replicate (i + 1) (n + 1)) =
        FWr n (List.replicate i (n + 1)) ++ (1 :: (List.replicate s.length 3 ++ [3])) := by
      show FWr n (List.replicate i (n + 1)) ++ blkW n (n + 1) = _
      rw [blkW_full, hn, rep_snoc_eq, List.replicate_succ]
    have hA := blkCopyP Kl (b :: Kr') a s _ hKl hKr ha hs hT
    have hS := blkDecStep Kl Kr' a s t (FWr n (List.replicate i (n + 1))) b hKl hKr.tail ha hs ht
      hBl hKr.head
    have h2 := ih (Kl ++ [b]) (i + 1) (hKl.snoc hKr.head) hKr.tail
    have e : i + 1 + Kr'.length + 1 = i + (b :: Kr').length + 1 := by
      simp only [List.length_cons]; omega
    rw [e] at h2
    have hX : NoB (1 :: (Kr' ++ 1 :: (a ++ 1 :: (s ++ 1 :: 1 :: (t ++ 1 :: (FWr n (List.replicate i (n + 1)) ++
        1 :: (List.replicate s.length 3 ++ [3]))))))) := by
      have h1 : NoB (List.replicate s.length 3 ++ [3]) :=
        (t3_noB (rep_t3 _)).app (NoB.cons (by simp [NB]) NoB.nil)
      have h2 : NoB (FWr n (List.replicate i (n + 1)) ++ 1 :: (List.replicate s.length 3 ++ [3])) :=
        (o13_noB hBl).app (NoB.cons one_nb h1)
      have h3 : NoB (t ++ 1 :: (FWr n (List.replicate i (n + 1)) ++ 1 :: (List.replicate s.length 3 ++ [3]))) :=
        (t3_noB ht).app (NoB.cons one_nb h2)
      exact NoB.cons one_nb (hKr.tail.noB.app (NoB.cons one_nb (ha.noB.app (NoB.cons one_nb
        (hs.noB.app (NoB.cons one_nb (NoB.cons one_nb h3)))))))
    have hW := grbWalk (Kl ++ [b]) _ [] (Sym4.app hKl.sym4 (Sym4.cons (bits_all hKr.head) Sym4.nil))
      hX Sym4.nil
    simp only [List.append_nil] at hW
    refine hA.trans ((hS.of_eq (by simp) rfl).trans (hW.trans
      (h2.of_eq ?_ (by simp))))
    rw [eF]

end ZP.Poly
