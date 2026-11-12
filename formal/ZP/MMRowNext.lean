module

public import ZP.MMRowFin

@[expose] public section

/-! After a correct row: the Q pass loads the next `out` row, then either `A` is used up (`rowDoneUsed`: outcome 1 up to
`DP31`) or `B` is shifted back (`rowDoneMore`). -/

namespace ZP.Mul.MM

open ZP

theorem bits_rep2 (m : Nat) : Bits (List.replicate m 2) := fun a ha => by
  rw [List.eq_of_mem_replicate ha]; simp [bits]

theorem rowDoneUsed' (q m : Nat) (Bd Os Cb0 J sv Y2 Rest : List Nat) (e : Nat) (hBd : Bits Bd) (hOs : Bits Os)
    (hCb0 : ∀ a ∈ Cb0, a = 0) (hJ : Bits J) (hsv : Bits sv) (hY2 : Sym4 Y2) (he : e = 0 ∨ e = 1)
    (hRest : Sym4 Rest) (hER : Cb0 ++ (1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2) = e :: Rest) :
    zmmLogic.Reach
      (hdR QMM.RS1 (List.replicate q 1 ++ 1 :: 0 :: (Bd ++ [1]))
        (0 :: List.replicate m 2 ++ 1 :: (Os ++ Cb0 ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2)))
      (hdR Q.DP31 (1 :: (J ++ 1 :: (sv ++ [1]))) (1 :: Y2)) := by
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have h1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have hq : Sym4 (List.replicate q 1) := sym4_rep q 1 h1
  have hOe : Sym4 (Os ++ e :: Rest) := by
    refine Sym4.app hOs.sym4 (Sym4.cons ?_ hRest)
    rcases he with rfl | rfl <;> simp [ALL]
  have hCbs : ∀ a ∈ Cb0, a ∈ B0 := fun a ha => by simp [B0, hCb0 a ha]
  have eR : Os ++ Cb0 ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2 = Os ++ e :: Rest := by
    rw [← hER]; simp
  have s0 := rowFinOK (List.replicate q 1) Bd (List.replicate m 2) (Os ++ e :: Rest) hq hBd
    (fun a ha => List.eq_of_mem_replicate ha) (bits_rep2 m) hOe
  have hA : Sym4 (List.replicate q 1 ++ 1 :: 0 :: Bd ++ [1]) := by
    have := hBd.sym4
    simp [sym4_app_iff, sym4_cons_iff, *]
  have s1 := qPass _ hA m [] Os Rest e he Bits.nil hOs hRest
  obtain ⟨Cn, hCn⟩ : ∃ Cn, Cn = ((Os.reverse ++ List.replicate m 2).take m).reverse := ⟨_, rfl⟩
  rw [← hCn] at s1
  have hCnb : Bits Cn := fun a ha => by
    rw [hCn, List.mem_reverse] at ha
    have := List.mem_of_mem_take ha
    rw [List.mem_append, List.mem_reverse] at this
    rcases this with h | h
    · exact hOs a h
    · rw [List.eq_of_mem_replicate h]; simp [bits]
  have hout : Bits (Os.take (Os.length - m)) := fun a ha => hOs a (List.mem_of_mem_take ha)
  have hCb : ∀ a ∈ (List.replicate (min m Os.length) 0 ++ Cb0), a ∈ B0 := fun a ha => by
    rcases List.mem_append.mp ha with h | h
    · rw [List.eq_of_mem_replicate h]; simp [B0]
    · exact hCbs a h
  have s2 := nUsed q Bd Cn (Os.take (Os.length - m)) (List.replicate (min m Os.length) 0 ++ Cb0) J sv Y2
    hBd hCnb hout hCb hJ hsv hY2
  have s3 := vw1Ok (List.replicate q 0 ++ 0 :: 0 :: List.replicate Bd.length 0 ++
      0 :: 0 :: List.replicate Cn.length 0) (Os.take (Os.length - m)) (List.replicate (min m Os.length) 0 ++ Cb0)
    J sv Y2 (by
      intro a ha
      simp [List.mem_replicate] at ha
      omega) (by simp; omega) hout hCb hJ hsv hY2
  have e2 := hd_cons0 QMM.Q2 (List.replicate q 1 ++ 1 :: 0 :: Bd) (0 :: Cn ++ [] ++ 1 :: (Os.take (Os.length - m) ++
    List.replicate (min m Os.length) 0 ++ e :: Rest)) 1
  rw [← e2] at s1
  rw [← hER] at s0 s1
  simp only [List.length_replicate, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at s0 s1 s2 s3 ⊢
  exact s0.trans (s1.trans (s2.trans s3))

theorem rowDoneUsed (q m : Nat) (Bd Os Cb0 J sv Y2 : List Nat) (hBd : Bits Bd) (hOs : Bits Os)
    (hCb0 : ∀ a ∈ Cb0, a = 0) (hJ : Bits J) (hsv : Bits sv) (hY2 : Sym4 Y2) :
    zmmLogic.Reach
      (hdR QMM.RS1 (List.replicate q 1 ++ 1 :: 0 :: (Bd ++ [1]))
        (0 :: List.replicate m 2 ++ 1 :: (Os ++ Cb0 ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2)))
      (hdR Q.DP31 (1 :: (J ++ 1 :: (sv ++ [1]))) (1 :: Y2)) := by
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have h1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have hJ4 := hJ.sym4
  have hs4 := hsv.sym4
  cases Cb0 with
  | nil =>
    exact rowDoneUsed' q m Bd Os [] J sv Y2 (J ++ 1 :: sv ++ 0 :: 1 :: Y2) 1 hBd hOs hCb0 hJ hsv hY2
      (Or.inr rfl) (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp)
  | cons c Cb0 =>
    have hc : c = 0 := hCb0 c (by simp)
    subst hc
    exact rowDoneUsed' q m Bd Os (0 :: Cb0) J sv Y2 (Cb0 ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2) 0 hBd hOs hCb0 hJ hsv hY2
      (Or.inl rfl) (by
        have : Sym4 Cb0 := fun a ha => by rw [hCb0 a (by simp [ha])]; simp [ALL]
        simp [sym4_app_iff, sym4_cons_iff, *]) (by simp)

theorem rowDoneMore (Au Bd' Os Rest : List Nat) (x x1 q m e : Nat) (hAu : Bits Au) (hx : x ∈ bits) (hx1 : x1 ∈ bits)
    (hBd : Bits Bd') (hOs : Bits Os) (he : e = 0 ∨ e = 1) (hRest : Sym4 Rest) :
    zmmLogic.Reach
      (hdR QMM.RS1 (Au ++ x :: List.replicate q 1 ++ 1 :: 0 :: (x1 :: Bd' ++ [1]))
        (0 :: List.replicate m 2 ++ 1 :: (Os ++ e :: Rest)))
      (hdR QMM.RS1 (Au ++ x :: List.replicate q 1 ++ 1 :: x1 :: Bd' ++ [0, 1])
        (0 :: ((Os.reverse ++ List.replicate m 2).take m).reverse ++ [] ++
          1 :: (Os.take (Os.length - m) ++ List.replicate (min m Os.length) 0 ++ e :: Rest))) := by
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have h1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have hrep : Sym4 (List.replicate q 1) := sym4_rep q 1 h1
  have hx4 : x ∈ ALL := by rcases mem_bits hx with rfl | rfl <;> simp [ALL]
  have hq : Sym4 (Au ++ x :: List.replicate q 1) := by
    have := hAu.sym4
    simp [sym4_app_iff, sym4_cons_iff, *]
  have hOe : Sym4 (Os ++ e :: Rest) := by
    refine Sym4.app hOs.sym4 (Sym4.cons ?_ hRest)
    rcases he with rfl | rfl <;> simp [ALL]
  have hBd1 : Bits (x1 :: Bd') := Bits.cons hx1 hBd
  have s0 := rowFinOK (Au ++ x :: List.replicate q 1) (x1 :: Bd') (List.replicate m 2) (Os ++ e :: Rest) hq hBd1
    (fun a ha => List.eq_of_mem_replicate ha) (bits_rep2 m) hOe
  have hA : Sym4 (Au ++ x :: List.replicate q 1 ++ 1 :: 0 :: (x1 :: Bd') ++ [1]) := by
    have h3 := hBd1.sym4
    have h4 := hAu.sym4
    have h5 : x1 ∈ ALL := by rcases mem_bits hx1 with rfl | rfl <;> simp [ALL]
    have h6 := hBd.sym4
    simp [sym4_app_iff, sym4_cons_iff, *]
  have s1 := qPass _ hA m [] Os Rest e he Bits.nil hOs hRest
  have hR1 : Sym4 (0 :: ((Os.reverse ++ List.replicate m 2).take m).reverse ++ [] ++
      1 :: (Os.take (Os.length - m) ++ List.replicate (min m Os.length) 0 ++ e :: Rest)) := by
    have h2 : ∀ a ∈ ((Os.reverse ++ List.replicate m 2).take m).reverse, a ∈ ALL := by
      intro a ha
      rw [List.mem_reverse] at ha
      have := List.mem_of_mem_take ha
      rw [List.mem_append, List.mem_reverse] at this
      rcases this with h | h
      · exact hOs.sym4 a h
      · rw [List.eq_of_mem_replicate h]; simp [ALL]
    have h3 : ∀ a ∈ Os.take (Os.length - m), a ∈ ALL := fun a ha => hOs.sym4 a (List.mem_of_mem_take ha)
    have h4 : ∀ a ∈ List.replicate (min m Os.length) 0, a ∈ ALL := fun a ha => by
      rw [List.eq_of_mem_replicate ha]; simp [ALL]
    have h5 : e ∈ ALL := by rcases he with rfl | rfl <;> simp [ALL]
    simp [sym4_app_iff, sym4_cons_iff, h0, h1, h5]
    exact ⟨h2, h3, h4, hRest⟩
  have s2 := nMore Au Bd' _ q x x1 hAu.sym4 hx hx1 hBd hR1
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at s0 s1 s2 ⊢
  exact s0.trans (s1.trans s2)

end ZP.Mul.MM
