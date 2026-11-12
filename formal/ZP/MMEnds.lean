module

public import ZP.MMVerdict
public import ZP.MMVerdict3
public import ZP.MMDryRow

@[expose] public section

/-! Verdict exits ending in `DP31` / `DP30` (verdict wrappers). -/

namespace ZP.Mul.MM

open ZP

theorem zeros_mem (n : Nat) : ∀ a ∈ List.replicate n 0, a = 0 := fun a ha => List.eq_of_mem_replicate ha

set_option maxHeartbeats 1000000 in
theorem endFA1 (Bpr ARr ALr outr Cb J sv Y2 : List Nat) (hBpr : Bits Bpr) (hARr : Bits ARr) (hALr : Bits ALr)
    (houtr : Bits outr) (hCb : ∀ a ∈ Cb, a ∈ B0) (hJ : Bits J) (hsv : Bits sv) (hY2 : Sym4 Y2) :
    zmmLogic.Reach (hdR QMM.FA [] (0 :: 0 :: (Bpr ++ 1 :: (ARr ++ 0 :: (ALr ++ 1 :: (outr ++ (Cb ++ 1 :: (J ++ 1 :: (sv ++ 0 :: 1 :: Y2)))))))))
      (hdR Q.DP31 (1 :: (J ++ 1 :: (sv ++ [1]))) (1 :: Y2)) := by
  have h1 := vEndShortFA1 [] Bpr ARr ALr outr Cb J sv Y2 Bits.nil.noB hBpr hARr hALr houtr hCb hJ hsv hY2
  have h2 := vw1Ok (0 :: (List.replicate Bpr.length 0 ++ 0 :: (List.replicate ARr.length 0 ++ 0 :: List.replicate ALr.length 0)))
    outr Cb J sv Y2 (by intro a ha; simp at ha; rcases ha with rfl | ha | rfl | ha | rfl | ha <;> simp_all [List.eq_of_mem_replicate])
    (by simp; omega) houtr hCb hJ hsv hY2
  exact (h1.of_eq (by simp) rfl).trans (h2.of_eq (by simp) rfl)

set_option maxHeartbeats 1000000 in
theorem endJ11 (Bpr ARr ALr outr Cb J sv Y2 : List Nat) (hBpr : Bits Bpr) (hARr : Bits ARr) (hALr : Bits ALr)
    (houtr : Bits outr) (hCb : ∀ a ∈ Cb, a ∈ B0) (hJ : Bits J) (hsv : Bits sv) (hY2 : Sym4 Y2) :
    zmmLogic.Reach (hdR QMM.J1 [] (0 :: 0 :: (Bpr ++ 1 :: (ARr ++ 0 :: (ALr ++ 1 :: (outr ++ (Cb ++ 1 :: (J ++ 1 :: (sv ++ 0 :: 1 :: Y2)))))))))
      (hdR Q.DP31 (1 :: (J ++ 1 :: (sv ++ [1]))) (1 :: Y2)) := by
  have h1 := vEndShortJ11 [] Bpr ARr ALr outr Cb J sv Y2 Bits.nil.noB hBpr hARr hALr houtr hCb hJ hsv hY2
  have h2 := vw1Ok (0 :: (List.replicate Bpr.length 0 ++ 0 :: (List.replicate ARr.length 0 ++ 0 :: List.replicate ALr.length 0)))
    outr Cb J sv Y2 (by intro a ha; simp at ha; rcases ha with rfl | ha | rfl | ha | rfl | ha <;> simp_all [List.eq_of_mem_replicate])
    (by simp; omega) houtr hCb hJ hsv hY2
  exact (h1.of_eq (by simp) rfl).trans (h2.of_eq (by simp) rfl)

set_option maxHeartbeats 1000000 in
theorem endEmpty (outr Cb J sv Y2 : List Nat) (houtr : Bits outr) (hCb : ∀ a ∈ Cb, a ∈ B0) (hJ : Bits J) (hsv : Bits sv) (hY2 : Sym4 Y2) :
    zmmLogic.Reach (hdR QMM.X3a [] (0 :: 1 :: (outr ++ (Cb ++ 1 :: (J ++ 1 :: (sv ++ 0 :: 1 :: Y2))))))
      (hdR Q.DP31 (1 :: (J ++ 1 :: (sv ++ [1]))) (1 :: Y2)) := by
  have h1 := vSetupEmpty [] [] outr Cb J sv Y2 Bits.nil (by simp) houtr hCb hJ hsv hY2
  have h2 := vw1Ok [0, 0, 0] outr Cb J sv Y2 (by simp) (by simp) houtr hCb hJ hsv hY2
  exact h1.trans (h2.of_eq (by simp) rfl)

set_option maxHeartbeats 1000000 in
theorem endZero (wr outr Cb J sv Y2 : List Nat) (hwr : Bits wr) (houtr : Bits outr) (hCb : ∀ a ∈ Cb, a ∈ B0) (hJ : Bits J) (hsv : Bits sv) (hY2 : Sym4 Y2) :
    zmmLogic.Reach (hdR QMM.X3a wr (2 :: 1 :: (outr ++ (Cb ++ 1 :: (J ++ 1 :: (sv ++ 0 :: 1 :: Y2))))))
      (hdR Q.DP31 (1 :: (J ++ 1 :: (sv ++ [1]))) (1 :: Y2)) := by
  have h1 := vSetupZero wr [] outr Cb J sv Y2 hwr (by simp) houtr hCb hJ hsv hY2
  have h2 := vw1Ok (0 :: 0 :: 0 :: (List.replicate wr.length 0 ++ [0])) outr Cb J sv Y2
    (by intro a ha; simp only [List.mem_cons, List.mem_append, List.mem_singleton] at ha; rcases ha with h | h | h | h | h | h <;> first | exact h | exact List.eq_of_mem_replicate h | exact absurd h List.not_mem_nil) (by simp) houtr hCb hJ hsv hY2
  exact h1.trans (h2.of_eq (by simp) rfl)

set_option maxHeartbeats 1000000 in
theorem endOnes (on outr Cb J sv Y2 : List Nat) (hon : ∀ a ∈ on, a ∈ T3) (houtr : Bits outr) (hCb : ∀ a ∈ Cb, a ∈ B0) (hJ : Bits J) (hsv : Bits sv) (hY2 : Sym4 Y2) :
    zmmLogic.Reach (hdR QMM.X3 [] (0 :: (on ++ 1 :: (outr ++ (Cb ++ 1 :: (J ++ 1 :: (sv ++ 0 :: 1 :: Y2)))))))
      (hdR Q.DP31 (1 :: (J ++ 1 :: (sv ++ [1]))) (1 :: Y2)) := by
  have h1 := vSetupOnes [] on outr Cb J sv Y2 Bits.nil hon houtr hCb hJ hsv hY2
  have h2 := vw1Ok (0 :: 0 :: 0 :: List.replicate on.length 0) outr Cb J sv Y2
    (by intro a ha; simp only [List.mem_cons] at ha; rcases ha with h | h | h | h <;> first | exact h | exact List.eq_of_mem_replicate h) (by simp) houtr hCb hJ hsv hY2
  exact h1.trans (h2.of_eq (by simp) rfl)

set_option maxHeartbeats 1000000 in
theorem endNoW (on outr Cb J sv Y2 : List Nat) (hon : ∀ a ∈ on, a ∈ T3) (houtr : Bits outr) (hCb : ∀ a ∈ Cb, a ∈ B0) (hJ : Bits J) (hsv : Bits sv) (hY2 : Sym4 Y2) :
    zmmLogic.Reach (hdR QMM.SM [] (0 :: 0 :: (on ++ 1 :: (outr ++ (Cb ++ 1 :: (J ++ 1 :: (sv ++ 0 :: 1 :: Y2)))))))
      (hdR Q.DP31 (1 :: (J ++ 1 :: (sv ++ [1]))) (1 :: Y2)) := by
  have h1 := vSetupNoW [] on outr Cb J sv Y2 Bits.nil hon houtr hCb hJ hsv hY2
  have h2 := vw1Ok (0 :: 0 :: 0 :: List.replicate on.length 0) outr Cb J sv Y2
    (by intro a ha; simp only [List.mem_cons] at ha; rcases ha with h | h | h | h <;> first | exact h | exact List.eq_of_mem_replicate h) (by simp) houtr hCb hJ hsv hY2
  exact h1.trans (h2.of_eq (by simp) rfl)

end ZP.Mul.MM
