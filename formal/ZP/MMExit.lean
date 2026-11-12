module

public import ZP.MMDry2
public import ZP.MMVerdict2
public import ZP.MMVerdict

@[expose] public section

/-! Row-level exits to the verdict: `A` used up after a row (`nUsed`). -/

namespace ZP.Mul.MM

open ZP

theorem sym4_B0 {Cb : List Nat} (h : ∀ a ∈ Cb, a ∈ B0) : Sym4 Cb := fun a ha => by
  have := h a ha
  simp only [B0, List.mem_singleton] at this
  subst this
  simp [ALL]

/-- After the Q pass: `N1`-`N3` find the consumed `M`s and then a blank (`A` used up): outcome 1, up to `VW1`. -/
theorem nUsed (q : Nat) (Bpr ALr outr Cb J sv Y2 : List Nat) (hBpr : Bits Bpr) (hALr : Bits ALr)
    (houtr : Bits outr) (hCb : ∀ a ∈ Cb, a ∈ B0) (hJ : Bits J) (hsv : Bits sv) (hY2 : Sym4 Y2) :
    zmmLogic.Reach
      (hd QMM.Q2 ([0] ++ List.replicate q 1 ++ [1, 0] ++ Bpr ++ [1])
        (0 :: ALr ++ 1 :: outr ++ Cb ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2))
      (hdR QMM.VW1 [0] (List.replicate (List.replicate q 1).length 0 ++ 0 :: 0 :: List.replicate Bpr.length 0 ++
        0 :: 0 :: List.replicate ALr.length 0 ++ 3 :: outr ++ Cb ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2)) := by
  have hB4 := hBpr.sym4
  have hA4 := hALr.sym4
  have ho4 := houtr.sym4
  have hC4 := sym4_B0 hCb
  have hJ4 := hJ.sym4
  have hs4 := hsv.sym4
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have h1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have hq : Sym4 (List.replicate q 1) := sym4_rep q 1 h1
  have hR : Sym4 (0 :: ALr ++ 1 :: outr ++ Cb ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2) := by
    simp [sym4_app_iff, sym4_cons_iff, *]
  have t0 := q2M ([0] ++ List.replicate q 1 ++ [1, 0] ++ Bpr)
    (0 :: ALr ++ 1 :: outr ++ Cb ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) hR
  have t1 := n1Loop Bpr hBpr ([0] ++ List.replicate q 1 ++ [1, 0])
    (1 :: 0 :: ALr ++ 1 :: outr ++ Cb ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have t2 := n1End ([0] ++ List.replicate q 1 ++ [1])
    (Bpr ++ 1 :: 0 :: ALr ++ 1 :: outr ++ Cb ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have t3 := n2M ([0] ++ List.replicate q 1)
    (0 :: Bpr ++ 1 :: 0 :: ALr ++ 1 :: outr ++ Cb ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have t4 := n3Loop q [0] (1 :: 0 :: Bpr ++ 1 :: 0 :: ALr ++ 1 :: outr ++ Cb ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have e4 := hd_snoc QMM.N3 [] (List.replicate q 1 ++ (1 :: 0 :: Bpr ++ 1 :: 0 :: ALr ++ 1 :: outr ++ Cb ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2)) 0
  simp only [List.nil_append] at e4
  rw [e4] at t4
  have t5 := vEndUsed (List.replicate q 1) Bpr ALr outr Cb J sv Y2
    (fun a ha => by rw [List.eq_of_mem_replicate ha]; simp [M1s]) hBpr hALr houtr hCb hJ hsv hY2
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at t0 t1 t2 t3 t4 t5 ⊢
  exact t0.trans (t1.trans (t2.trans (t3.trans (t4.trans t5))))

end ZP.Mul.MM
