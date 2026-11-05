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


theorem rep_sym4 (k c : Nat) (hc : c ∈ ALL) : Sym4 (List.replicate k c) := fun a ha => by
  rw [List.eq_of_mem_replicate ha]; exact hc

theorem bits_app {a b : List Nat} (ha : Bits a) (hb : Bits b) : Bits (a ++ b) := fun x hx => by
  rcases List.mem_append.1 hx with h | h
  · exact ha x h
  · exact hb x h

/-- One iteration of the row part, from the marking of a cell of `m` to the test of `m`. -/
theorem rowIterA (ms : List Nat) (ws xs : List (List Nat)) (Rt : List Nat)
    (hms : ∀ e ∈ ms, 1 ≤ e) (hws : ∀ e ∈ ws, Bits e ∧ e ≠ []) (hxs : ∀ e ∈ xs, Bits e ∧ e ≠ []) (hR : Sym4 Rt)
    (i n p q : Nat) (pasT HU : List (List Nat)) (hp : ∀ t ∈ pasT, Bits t) (hh : ∀ t ∈ HU, Bits t)
    (hn : i + n ≤ HU.length) :
    zgiLogic.Reach
      (hd QG.gTR1 (MEnc ms ++ List.replicate i 2 ++ 3 :: (List.replicate n 3 ++ 1 :: (MEs ws ++ 1 :: List.replicate p 3)))
        (2 :: (List.replicate q 2 ++ 1 :: (MEs xs ++ 1 :: (MP pasT ++ MU HU ++ Rt)))))
      (hdR QG.gD2 (MEnc ms ++ List.replicate (i + n) 2 ++ [3] ++ 1 :: (MEs ws ++ [1]))
        (List.replicate p 3 ++ (List.replicate (q + 1) 2 ++ 1 :: (MEs xs ++ 1 ::
          (MP (pasT ++ HU.take (i + n)) ++ MU (HU.drop (i + n)) ++ Rt))))) := by
  have sW := MEs_sym4 ws (fun e he => (hws e he).1)
  have sX := MEs_sym4 xs (fun e he => (hxs e he).1)
  have sP := MP_sym4 pasT hp
  have sU := MU_sym4 HU hh
  have hQ : NoB (List.replicate n 3 ++ 1 :: (MEs ws ++ 1 :: List.replicate p 3)) := by
    have := MEs_noB ws (fun e he => (hws e he).1)
    simp [NB, this]
  have hR' : Sym4 (List.replicate q 2 ++ 1 :: (MEs xs ++ 1 :: (MP pasT ++ MU HU ++ Rt))) := by
    simp [ALL, sX, sP, sU, hR, rep_sym4 q 2 (by simp [ALL])]
  have h1 := rowReset ms hms i _ _ hQ hR'
  have hmb : Bits (List.replicate p 3 ++ List.replicate (q + 1) 2) := bits_app (bits_rep3 p) (bits_rep2 (q + 1))
  have h2 := innerLoopP QG.gIL1 (Or.inr rfl) ms ws xs (List.replicate p 3 ++ List.replicate (q + 1) 2) Rt
    hms hws hmb hxs hR (i + n) 0 pasT HU hp hh hn
  have sMb : Sym4 (List.replicate p 3 ++ List.replicate (q + 1) 2) := hmb.sym4
  have hp' : ∀ t ∈ pasT ++ HU.take (i + n), Bits t := by
    intro t ht
    rcases List.mem_append.1 ht with h | h
    · exact hp t h
    · exact hh t (List.mem_of_mem_take h)
  have hh' : ∀ t ∈ HU.drop (i + n), Bits t := fun t ht => hh t (List.mem_of_mem_drop ht)
  have sR2 : Sym4 ((List.replicate p 3 ++ List.replicate (q + 1) 2) ++ 1 :: (MEs xs ++ 1 ::
      (MP (pasT ++ HU.take (i + n)) ++ MU (HU.drop (i + n)) ++ Rt))) :=
    sMb.app (Sym4.cons (by simp [ALL]) (sX.app (Sym4.cons (by simp [ALL])
      (((MP_sym4 _ hp').app (MU_sym4 _ hh')).app hR))))
  have sP0 : Sym4 (MEnc ms ++ List.replicate (0 + (i + n)) 2 ++ [3]) :=
    ((MEnc_sym4 ms).app (Sym4.rep _ _ (by simp [ALL]))).app (by simp [ALL])
  have sRh : Sym4 (MEs ws ++ 1 :: ((List.replicate p 3 ++ List.replicate (q + 1) 2) ++ 1 :: (MEs xs ++ 1 ::
      (MP (pasT ++ HU.take (i + n)) ++ MU (HU.drop (i + n)) ++ Rt)))) :=
    sW.app (Sym4.cons (by simp [ALL]) sR2)
  have h3 := wd1EndIn (MEnc ms ++ List.replicate (0 + (i + n)) 2 ++ [3])
    (MEs ws ++ 1 :: ((List.replicate p 3 ++ List.replicate (q + 1) 2) ++ 1 :: (MEs xs ++ 1 ::
      (MP (pasT ++ HU.take (i + n)) ++ MU (HU.drop (i + n)) ++ Rt)))) sP0 sRh
  have h4 := wd1Walk _ sR2 ws (MEnc ms ++ List.replicate (0 + (i + n)) 2 ++ [3] ++ [1]) hws (sP0.app (by simp [ALL]))
  have e1 : List.replicate i 3 ++ 3 :: (List.replicate n 3 ++ 1 :: (MEs ws ++ 1 :: List.replicate p 3) ++ 2 :: (List.replicate q 2 ++ 1 :: (MEs xs ++ 1 :: (MP pasT ++ MU HU ++ Rt))))
      = List.replicate 0 2 ++ List.replicate (i + n + 1) 3 ++ 1 ::
        (MEs ws ++ 1 :: ((List.replicate p 3 ++ List.replicate (q + 1) 2) ++ 1 :: (MEs xs ++ 1 :: (MP pasT ++ MU HU ++ Rt)))) := by
    have : List.replicate (i + n + 1) 3 = List.replicate i 3 ++ 3 :: List.replicate n 3 := by
      rw [show i + n + 1 = i + (n + 1) from rfl, ← List.replicate_append_replicate, List.replicate_succ]
    rw [this]
    simp [List.replicate_succ, List.append_assoc]
  exact (((h1.of_eq rfl (by rw [e1])).trans h2).trans h3).trans (h4.of_eq rfl (by simp [List.append_assoc]))

/-- The whole row part: `m` iterations, each passing `nn = a - 1` entries of `H`. -/
theorem rowLoop (ms : List Nat) (ws xs : List (List Nat)) (Rt : List Nat)
    (hms : ∀ e ∈ ms, 1 ≤ e) (hws : ∀ e ∈ ws, Bits e ∧ e ≠ []) (hxs : ∀ e ∈ xs, Bits e ∧ e ≠ []) (hR : Sym4 Rt)
    (nn : Nat) : ∀ (p i n q : Nat) (pasT HU : List (List Nat)), i + n = nn →
    (∀ t ∈ pasT, Bits t) → (∀ t ∈ HU, Bits t) → (p + 1) * nn ≤ HU.length →
    zgiLogic.Reach
      (hd QG.gTR1 (MEnc ms ++ List.replicate i 2 ++ 3 :: (List.replicate n 3 ++ 1 :: (MEs ws ++ 1 :: List.replicate p 3)))
        (2 :: (List.replicate q 2 ++ 1 :: (MEs xs ++ 1 :: (MP pasT ++ MU HU ++ Rt)))))
      (hd QG.gGL (MEnc ms ++ List.replicate nn 2 ++ 3 :: 1 :: MEs ws)
        (1 :: (List.replicate (p + q + 1) 2 ++ 1 :: (MEs xs ++ 1 ::
          (MP (pasT ++ HU.take ((p + 1) * nn)) ++ MU (HU.drop ((p + 1) * nn)) ++ Rt))))) := by
  intro p
  induction p with
  | zero =>
    intro i n q pasT HU hin hp hh hlen
    subst hin
    have h1 := rowIterA ms ws xs Rt hms hws hxs hR i n 0 q pasT HU hp hh (by simpa using hlen)
    have sX := MEs_sym4 xs (fun e he => (hxs e he).1)
    have hp' : ∀ t ∈ pasT ++ HU.take (i + n), Bits t := by
      intro t ht
      rcases List.mem_append.1 ht with h | h
      · exact hp t h
      · exact hh t (List.mem_of_mem_take h)
    have hh' : ∀ t ∈ HU.drop (i + n), Bits t := fun t ht => hh t (List.mem_of_mem_drop ht)
    have hS : Sym4 (MEs xs ++ 1 :: (MP (pasT ++ HU.take (i + n)) ++ MU (HU.drop (i + n)) ++ Rt)) :=
      sX.app (Sym4.cons (by simp [ALL]) (((MP_sym4 _ hp').app (MU_sym4 _ hh')).app hR))
    have hP : Sym4 (MEnc ms ++ List.replicate (i + n) 2 ++ [3] ++ 1 :: (MEs ws ++ [1])) := by
      have sW := MEs_sym4 ws (fun e he => (hws e he).1)
      exact (((MEnc_sym4 ms).app (Sym4.rep _ _ (by simp [ALL]))).app (by simp [ALL])).app
        (Sym4.cons (by simp [ALL]) (sW.app (by simp [ALL])))
    have h2 := (gd2Row _ hS q 0 _ hP).2 (MEnc ms ++ List.replicate (i + n) 2 ++ [3] ++ 1 :: MEs ws) rfl (by simp)
    simp only [List.replicate, List.nil_append] at h1
    have := h1.trans h2
    simpa [Nat.zero_add, Nat.one_mul, List.append_assoc] using this
  | succ p ih =>
    intro i n q pasT HU hin hp hh hlen
    subst hin
    have h1 := rowIterA ms ws xs Rt hms hws hxs hR i n (p + 1) q pasT HU hp hh (by
      have : i + n ≤ (p + 1 + 1) * (i + n) := Nat.le_mul_of_pos_left _ (by omega)
      omega)
    have sX := MEs_sym4 xs (fun e he => (hxs e he).1)
    have hp' : ∀ t ∈ pasT ++ HU.take (i + n), Bits t := by
      intro t ht
      rcases List.mem_append.1 ht with h | h
      · exact hp t h
      · exact hh t (List.mem_of_mem_take h)
    have hh' : ∀ t ∈ HU.drop (i + n), Bits t := fun t ht => hh t (List.mem_of_mem_drop ht)
    have hS : Sym4 (MEs xs ++ 1 :: (MP (pasT ++ HU.take (i + n)) ++ MU (HU.drop (i + n)) ++ Rt)) :=
      sX.app (Sym4.cons (by simp [ALL]) (((MP_sym4 _ hp').app (MU_sym4 _ hh')).app hR))
    have hP : Sym4 (MEnc ms ++ List.replicate (i + n) 2 ++ [3] ++ 1 :: (MEs ws ++ [1])) := by
      have sW := MEs_sym4 ws (fun e he => (hws e he).1)
      exact (((MEnc_sym4 ms).app (Sym4.rep _ _ (by simp [ALL]))).app (by simp [ALL])).app
        (Sym4.cons (by simp [ALL]) (sW.app (by simp [ALL])))
    have h2 := (gd2Row _ hS q (p + 1) _ hP).1 p rfl
    have h3 := ih (i + n) 0 (q + 1) (pasT ++ HU.take (i + n)) (HU.drop (i + n)) (by omega) hp' hh' (by
      rw [List.length_drop]
      have : (p + 1 + 1) * (i + n) = (p + 1) * (i + n) + (i + n) := by rw [Nat.succ_mul]
      omega)
    have e1 : (p + 1 + 1) * (i + n) = (i + n) + (p + 1) * (i + n) := by
      rw [Nat.succ_mul, Nat.add_comm]
    have e2 : p + 1 + q + 1 = p + (q + 1) + 1 := by omega
    rw [e1, e2, List.take_add]
    refine ((h1.trans h2).trans (h3.of_eq (by simp [List.append_assoc]) rfl)).of_eq rfl ?_
    simp [MP_append, List.append_assoc, List.drop_drop, Nat.add_comm]

theorem n2Cell (q : Nat) (hq : q = QG.gN2c ∨ q = QG.gN2d) (P R : List Nat) (b : Nat) (hb : b ∈ bits)
    (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR q P (b :: R)) (hdR QG.gN2c (P ++ [b]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  rcases mem_bits hb with rfl | rfl <;> rcases hq with rfl | rfl
  · exact checkFF (env := [P, R]) (E := []) (k := 3) (q' := QG.gN2c) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [P, R]) (E := []) (k := 3) (q' := QG.gN2c) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [P, R]) (E := []) (k := 3) (q' := QG.gN2c) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [P, R]) (E := []) (k := 3) (q' := QG.gN2c) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem n2EndIn (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gN2c P (1 :: R)) (hdR QG.gN2d (P ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem n2EndS (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gN2d P (1 :: R)) (hdR QG.gHU (P ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem n2Cells (R : List Nat) (hR : Sym4 R) : ∀ (c P : List Nat), Bits c → Sym4 P →
    zgiLogic.Reach (hdR QG.gN2c P (c ++ 1 :: R)) (hdR QG.gN2d (P ++ c ++ [1]) R)
  | [], P, _, hP => (n2EndIn P R hP hR).of_eq (by simp) (by simp)
  | b :: c, P, hc, hP => by
    have hb := hc b (List.mem_cons_self ..)
    have hc' : Bits c := fun a ha => hc a (List.mem_cons_of_mem _ ha)
    have h1 := n2Cell QG.gN2c (Or.inl rfl) P (c ++ 1 :: R) b hb hP (by simp [ALL, hR, hc'.sym4])
    have hP' : Sym4 (P ++ [b]) := by
      rcases mem_bits hb with rfl | rfl <;> simp [ALL, hP]
    have h2 := n2Cells R hR c (P ++ [b]) hc' hP'
    exact (h1.of_eq rfl rfl).trans (h2.of_eq rfl (by simp))

theorem n2Entry (c P R : List Nat) (hc : Bits c) (hne : c ≠ []) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gN2d P (c ++ 1 :: R)) (hdR QG.gN2d (P ++ c ++ [1]) R) := by
  cases c with
  | nil => exact absurd rfl hne
  | cons b c =>
    have hb := hc b (List.mem_cons_self ..)
    have hc' : Bits c := fun a ha => hc a (List.mem_cons_of_mem _ ha)
    have h1 := n2Cell QG.gN2d (Or.inr rfl) P (c ++ 1 :: R) b hb hP (by simp [ALL, hR, hc'.sym4])
    have hP' : Sym4 (P ++ [b]) := by
      rcases mem_bits hb with rfl | rfl <;> simp [ALL, hP]
    have h2 := n2Cells R hR c (P ++ [b]) hc' hP'
    exact (h1.of_eq rfl rfl).trans (h2.of_eq rfl (by simp))

theorem n2Walk (R : List Nat) (hR : Sym4 R) : ∀ (cs : List (List Nat)) (P : List Nat),
    (∀ c ∈ cs, Bits c ∧ c ≠ []) → Sym4 P →
    zgiLogic.Reach (hdR QG.gN2d P (MEs cs ++ 1 :: R)) (hdR QG.gHU (P ++ MEs cs ++ [1]) R)
  | [], P, _, hP => (n2EndS P R hP hR).of_eq (by simp [MEs]) (by simp [MEs])
  | c :: cs, P, h, hP => by
    obtain ⟨hc, hne⟩ := h c (List.mem_cons_self ..)
    have hcs : ∀ d ∈ cs, Bits d ∧ d ≠ [] := fun d hd => h d (List.mem_cons_of_mem _ hd)
    have hM : Sym4 (MEs cs ++ 1 :: R) := by
      have := MEs_sym4 cs (fun d hd => (hcs d hd).1)
      simp [ALL, this, hR]
    have h1 := n2Entry c P (MEs cs ++ 1 :: R) hc hne hP hM
    have hP' : Sym4 (P ++ c ++ [1]) := by simp [ALL, hP, hc.sym4]
    have h2 := n2Walk R hR cs _ hcs hP'
    exact (h1.of_eq (by simp [MEs, ME, List.append_assoc]) rfl).trans
      (h2.of_eq rfl (by simp [MEs, ME, List.append_assoc]))

theorem huUnm (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gHU P (2 :: R)) (hdR QG.gHU2 (P ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem huFound (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gHU P (3 :: R)) (hdR QG.gHC (P ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem huEndM (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gHU P (1 :: R)) (hdR QG.gFG (P ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem huEndB (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gHU P (0 :: R)) (hd QG.gFG P (0 :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 0, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 0, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem hu2Cell2 (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gHU2 P (2 :: R)) (hdR QG.gHU2 (P ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem hu2Cell3 (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gHU2 P (3 :: R)) (hdR QG.gHU2 (P ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem hu2M (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gHU2 P (1 :: R)) (hdR QG.gHU (P ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem hcMark (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gHC P (3 :: R)) (hd QG.gGL P (2 :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 2, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem hcFail2 (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gHC P (2 :: R)) (hdR QG.gFG (P ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem hcFail1 (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gHC P (1 :: R)) (hdR QG.gFG (P ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem hcFail0 (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gHC P (0 :: R)) (hd QG.gFG P (0 :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 0, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 0, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem hu2Cells (R : List Nat) (hR : Sym4 R) : ∀ (t P : List Nat), Bits t → Sym4 P →
    zgiLogic.Reach (hdR QG.gHU2 P (t ++ 1 :: R)) (hdR QG.gHU (P ++ t ++ [1]) R)
  | [], P, _, hP => (hu2M P R hP hR).of_eq (by simp) (by simp)
  | b :: t, P, ht, hP => by
    have hb := ht b (List.mem_cons_self ..)
    have ht' : Bits t := fun a ha => ht a (List.mem_cons_of_mem _ ha)
    have hR1 : Sym4 (t ++ 1 :: R) := by simp [ALL, hR, ht'.sym4]
    have hP' : Sym4 (P ++ [b]) := by
      rcases mem_bits hb with rfl | rfl <;> simp [ALL, hP]
    have h2 := hu2Cells R hR t (P ++ [b]) ht' hP'
    rcases mem_bits hb with rfl | rfl
    · exact ((hu2Cell2 P (t ++ 1 :: R) hP hR1).of_eq rfl rfl).trans (h2.of_eq rfl (by simp))
    · exact ((hu2Cell3 P (t ++ 1 :: R) hP hR1).of_eq rfl rfl).trans (h2.of_eq rfl (by simp))

/-- The passed entries are unmarked. -/
theorem huWalk (R : List Nat) (hR : Sym4 R) : ∀ (ts : List (List Nat)) (P : List Nat),
    (∀ t ∈ ts, Bits t) → Sym4 P →
    zgiLogic.Reach (hdR QG.gHU P (MP ts ++ R)) (hdR QG.gHU (P ++ MU ts) R)
  | [], P, _, _ => by simpa [MP, MU] using (LTM.Reach.refl _ _)
  | t :: ts, P, h, hP => by
    have ht := h t (List.mem_cons_self ..)
    have hts : ∀ u ∈ ts, Bits u := fun u hu => h u (List.mem_cons_of_mem _ hu)
    have hM : Sym4 (MP ts ++ R) := (MP_sym4 ts hts).app hR
    have h1 := huUnm P (t ++ 1 :: (MP ts ++ R)) hP (by simp [ALL, ht.sym4, hM])
    have hP1 : Sym4 (P ++ [3]) := by simp [ALL, hP]
    have h2 := hu2Cells (MP ts ++ R) hM t (P ++ [3]) ht hP1
    have hP2 : Sym4 (P ++ [3] ++ t ++ [1]) := by simp [ALL, hP, ht.sym4]
    have h3 := huWalk R hR ts _ hts hP2
    exact (h1.of_eq (by simp [MP]) rfl).trans ((h2.of_eq rfl rfl).trans (h3.of_eq rfl (by simp [MU, List.append_assoc])))

end ZP.G
