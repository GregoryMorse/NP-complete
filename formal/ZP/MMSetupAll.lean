module

public import ZP.MMDryRow
public import ZP.MMSetupSeg
public import ZP.MMLoops

@[expose] public section

/-! Setup: from the entry `mK1` to the dry row's first cycle. -/

namespace ZP.Mul.MM

open ZP

theorem hd_nil0M (q : Nat) (R : List Nat) : hd q [0] R = hd q [] R := rfl

theorem gcEndM (L Y : List Nat) (hL : Sym4 L) (hY : Sym4 Y) :
    zmmLogic.Reach (hdR Q.GC L (0 :: Y)) (hd QMM.X0 L (0 :: Y)) := by
  have hV : Valid [ALL, ALL] [L, Y] := Valid.cons hL (Valid.cons hY (Valid.nil _))
  have h : zmmLogic.Reach (hd Q.GC (L ++ [0]) Y) (hd QMM.X0 L (0 :: Y)) := checkTT (env := [L, Y]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 0]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 0, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  rw [hd_snoc] at h
  exact h

theorem sweepStep (q : Nat) (c : Nat) (hc : c ∈ bits) 
    (f2 : ∀ L R : List Nat, Sym4 L → Sym4 R → zmmLogic.Reach (hd q (L ++ [2]) R) (hd q L (2 :: R)))
    (f3 : ∀ L R : List Nat, Sym4 L → Sym4 R → zmmLogic.Reach (hd q (L ++ [3]) R) (hd q L (3 :: R)))
    (L R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zmmLogic.Reach (hd q (L ++ [c]) R) (hd q L (c :: R)) := by
  rcases mem_bits hc with rfl | rfl
  · exact f2 L R hL hR
  · exact f3 L R hL hR

theorem toX3a (Rw j s Y : List Nat) (hRw : Bits Rw) (hj : Bits j) (hs : Bits s) (hY : Sym4 Y) :
    zmmLogic.Reach (hdR QMM.mK1 [1] (Rw ++ 1 :: (j ++ 1 :: (s ++ 1 :: Y))))
      (hd QMM.X3a s.reverse (1 :: (Rw ++ 1 :: (j ++ 1 :: (s ++ 0 :: Y))))) := by
  have h1u : (1 : Nat) ∈ ALL := by simp [ALL]
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have hV : NoB (1 :: (Rw ++ 1 :: (j ++ [1]))) :=
    NoB.cons one_nb (hRw.noB.app (NoB.cons one_nb (hj.noB.app nb1)))
  have c1 := mkChain' Rw j s Y hRw hj hs hY
  have c2 := gcLoopM (1 :: (Rw ++ 1 :: (j ++ [1]))) Y hV hY s [] Bits.nil hs
  have hL : Sym4 (s.reverse ++ (1 :: (Rw ++ 1 :: (j ++ [1]))) ++ s) := by
    simp [sym4_app_iff, sym4_cons_iff, h1u, hs.rev.sym4, hRw.sym4, hj.sym4, hs.sym4]
  have c3 := gcEndM (s.reverse ++ (1 :: (Rw ++ 1 :: (j ++ [1]))) ++ s) Y hL hY
  have hSY : Sym4 Y := hY
  -- sweeps
  have s0 := fLoop QMM.X0 (fun c => c ∈ bits) (fun c hc => bits_all hc)
    (fun L R c hL hR hc => sweepStep QMM.X0 c hc x0Step2 x0Step3 L R hL hR) s (fun a ha => hs a ha)
    (s.reverse ++ (1 :: (Rw ++ 1 :: (j ++ [1])))) (0 :: Y)
    (by simp [sym4_app_iff, sym4_cons_iff, h1u, hs.rev.sym4, hRw.sym4, hj.sym4]) (Sym4.cons h0 hY)
  have hLs : Sym4 (s.reverse ++ (1 :: (Rw ++ 1 :: j))) := by
    simp [sym4_app_iff, sym4_cons_iff, h1u, hs.rev.sym4, hRw.sym4, hj.sym4]
  have s1 := x0End (s.reverse ++ (1 :: (Rw ++ 1 :: j))) (s ++ 0 :: Y) hLs
    (by simp [sym4_app_iff, sym4_cons_iff, h0, hs.sym4, hY])
  have s2 := fLoop QMM.X1 (fun c => c ∈ bits) (fun c hc => bits_all hc)
    (fun L R c hL hR hc => sweepStep QMM.X1 c hc x1Step2 x1Step3 L R hL hR) j (fun a ha => hj a ha)
    (s.reverse ++ (1 :: Rw) ++ [1]) (1 :: (s ++ 0 :: Y))
    (by simp [sym4_app_iff, sym4_cons_iff, h1u, hs.rev.sym4, hRw.sym4])
    (by simp [sym4_app_iff, sym4_cons_iff, h0, h1u, hs.sym4, hY])
  have s3 := x1End (s.reverse ++ (1 :: Rw)) (j ++ 1 :: (s ++ 0 :: Y))
    (by simp [sym4_app_iff, sym4_cons_iff, h1u, hs.rev.sym4, hRw.sym4])
    (by simp [sym4_app_iff, sym4_cons_iff, h0, h1u, hj.sym4, hs.sym4, hY])
  have s4 := fLoop QMM.X2 (fun c => c ∈ bits) (fun c hc => bits_all hc)
    (fun L R c hL hR hc => sweepStep QMM.X2 c hc x2Step2 x2Step3 L R hL hR) Rw (fun a ha => hRw a ha)
    (s.reverse ++ [1]) (1 :: (j ++ 1 :: (s ++ 0 :: Y)))
    (by simp [sym4_app_iff, sym4_cons_iff, h1u, hs.rev.sym4])
    (by simp [sym4_app_iff, sym4_cons_iff, h0, h1u, hj.sym4, hs.sym4, hY])
  have s5 := x2End s.reverse (Rw ++ 1 :: (j ++ 1 :: (s ++ 0 :: Y)))
    (hs.rev.sym4) (by simp [sym4_app_iff, sym4_cons_iff, h0, h1u, hRw.sym4, hj.sym4, hs.sym4, hY])
  have a1 := c1.trans ((c2.of_eq (by simp) (by simp)).trans c3)
  have a2 := a1.trans (s0.of_eq (by simp) rfl)
  have a3 := a2.trans (s1.of_eq (by simp) rfl)
  have a4 := a3.trans (s2.of_eq (by simp) rfl)
  have a5 := a4.trans (s3.of_eq (by simp) rfl)
  have a6 := a5.trans (s4.of_eq (by simp) rfl)
  exact (a6.trans (s5.of_eq (by simp) rfl)).of_eq rfl (by simp)


theorem setupFA (m : Nat) (w : List Nat) (T : List Nat) (hm : m ≠ 0) (hw : Bits w) (hwne : w ≠ []) (hT : Sym4 T) :
    zmmLogic.Reach (hd QMM.X3a (w.reverse ++ 2 :: List.replicate m 3) (1 :: T))
      (hd QMM.FA w.reverse (0 :: [] ++ 1 :: List.replicate m 3 ++ 0 :: 1 :: T)) := by
  have h1u : (1 : Nat) ∈ ALL := by simp [ALL]
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have h3u : (3 : Nat) ∈ ALL := by simp [ALL]
  have h2u : (2 : Nat) ∈ ALL := by simp [ALL]
  have hrep : Sym4 (List.replicate m 3) := fun a ha => by rw [List.eq_of_mem_replicate ha]; exact h3u
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨w0, wt, rfl⟩ : ∃ w0 wt, w = w0 :: wt := by
    cases w with
    | nil => exact absurd rfl hwne
    | cons a t => exact ⟨a, t, rfl⟩
  have hw0 : w0 ∈ bits := hw.head
  have hwt : Bits wt := hw.tail
  have hrep' : Sym4 (List.replicate m' 3) := fun a ha => by rw [List.eq_of_mem_replicate ha]; exact h3u
  have hwr : Sym4 (w0 :: wt).reverse := hw.rev.sym4
  have e1 : (w0 :: wt).reverse ++ 2 :: List.replicate (m' + 1) 3 =
      ((w0 :: wt).reverse ++ 2 :: List.replicate m' 3) ++ [3] := by
    simp [List.replicate_succ']
  have st1 := x3a3 ((w0 :: wt).reverse ++ 2 :: List.replicate m' 3) (1 :: T)
    (by simp [sym4_app_iff, sym4_cons_iff, h2u, hwt.rev.sym4, bits_all hw0, hrep']) (Sym4.cons h1u hT)
  have st2 := fLoop QMM.X3 (fun c => c = 3) (fun c hc => by rw [hc]; exact h3u)
    (fun L R c hL hR hc => by subst hc; exact x3Step L R hL hR) (List.replicate m' 3)
    (fun a ha => List.eq_of_mem_replicate ha) ((w0 :: wt).reverse ++ [2]) (3 :: 1 :: T)
    (by simp [sym4_app_iff, sym4_cons_iff, h2u, hwt.rev.sym4, bits_all hw0]) (Sym4.cons h3u (Sym4.cons h1u hT))
  have st3 := x3Hole (w0 :: wt).reverse (List.replicate m' 3 ++ 3 :: 1 :: T) hwr
    (by simp [sym4_app_iff, sym4_cons_iff, h1u, h3u, hrep', hT])
  have hwt4 : Sym4 wt.reverse := hwt.rev.sym4
  have hR3 : Sym4 (0 :: (List.replicate (m' + 1) 3 ++ 1 :: T)) := by
    simp [sym4_app_iff, sym4_cons_iff, h0, h1u, hT, hrep]
  -- SM: the first bit of w
  have st4 : zmmLogic.Reach (hd QMM.SM (wt.reverse ++ [w0]) (0 :: (List.replicate (m' + 1) 3 ++ 1 :: T)))
      (hd QMM.RB1 [] (wt.reverse ++ w0 :: 1 :: 0 :: (List.replicate (m' + 1) 3 ++ 1 :: T))) := by
    rcases mem_bits hw0 with rfl | rfl
    · have a1 := smStart0 wt.reverse (0 :: (List.replicate (m' + 1) 3 ++ 1 :: T)) hwt4 hR3
      have a2 := smLoop [] Sym4.nil wt.reverse hwt.rev (1 :: 0 :: (List.replicate (m' + 1) 3 ++ 1 :: T))
        (Sym4.cons h1u hR3) QMM.SM0 2 (Or.inl ⟨rfl, rfl⟩)
      simp only [List.nil_append, hd_zero_left] at a2
      exact a1.trans a2
    · have a1 := smStart1 wt.reverse (0 :: (List.replicate (m' + 1) 3 ++ 1 :: T)) hwt4 hR3
      have a2 := smLoop [] Sym4.nil wt.reverse hwt.rev (1 :: 0 :: (List.replicate (m' + 1) 3 ++ 1 :: T))
        (Sym4.cons h1u hR3) QMM.SM1 3 (Or.inr ⟨rfl, rfl⟩)
      simp only [List.nil_append, hd_zero_left] at a2
      exact a1.trans a2
  have hrB : Bits (List.replicate (m' + 1) 3) := fun a ha => by rw [List.eq_of_mem_replicate ha]; simp [bits]
  have rb := rbLoop2 [] Sym4.nil (w0 :: wt).reverse hw.rev (0 :: (List.replicate (m' + 1) 3 ++ 1 :: T)) hR3
  have hLq : Sym4 ((w0 :: wt).reverse ++ [0, 1]) := by
    simp [sym4_app_iff, sym4_cons_iff, h0, h1u, hwt.rev.sym4, bits_all hw0]
  have rs := rsLoop (List.replicate (m' + 1) 3) hrB ((w0 :: wt).reverse ++ [0, 1]) hLq T hT
  have fa := toFA (w0 :: wt).reverse [] (List.replicate (m' + 1) 3) T hwr Bits.nil hrB hT
  have e2 : List.replicate (m' + 1) 3 = List.replicate m' 3 ++ [3] := by simp [List.replicate_succ']
  have t1 : zmmLogic.Reach (hd QMM.X3a ((w0 :: wt).reverse ++ 2 :: List.replicate (m' + 1) 3) (1 :: T))
      (hd QMM.X3 ((w0 :: wt).reverse ++ 2 :: List.replicate m' 3) (3 :: 1 :: T)) := by rw [e1]; exact st1
  have t2 := t1.trans (st2.of_eq (by simp) rfl)
  have t3 := t2.trans (st3.of_eq (by simp) rfl)
  have t4 := t3.trans (st4.of_eq (by simp [e2]) rfl)
  have t5 := t4.trans (rb.of_eq (by simp [hd_nil0M]) rfl)
  have t6 := t5.trans (rs.of_eq (by simp) rfl)
  exact t6.trans (fa.of_eq (by simp) rfl)

end ZP.Mul.MM
