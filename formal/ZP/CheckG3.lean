module

public import ZP.CheckG2

@[expose] public section

/-! # The check phase of the GI machine (part 3): the `H` region with `c` passed entries -/

namespace ZP.G

open ZP

/-- The tape of `H` (entry tails `hs`, first cells `3`) in which the first `c` entries are passed
(first cell marked).  Entries are separated by `M`; the last one is followed by the blank. -/
def HP : List (List Nat) → Nat → List Nat
  | [], _ => []
  | [t], c => (if 0 < c then 2 else 3) :: t
  | t :: u :: ts, c => (if 0 < c then 2 else 3) :: (t ++ 1 :: HP (u :: ts) (c - 1))

theorem HP_sym4 : ∀ (hs : List (List Nat)) (c : Nat), (∀ t ∈ hs, Bits t) → Sym4 (HP hs c)
  | [], _, _ => Sym4.nil
  | [t], c, h => by
    have ht := h t (List.mem_cons_self ..)
    refine Sym4.cons ?_ ht.sym4
    split <;> simp [ALL]
  | t :: u :: ts, c, h => by
    have ht := h t (List.mem_cons_self ..)
    have := HP_sym4 (u :: ts) (c - 1) (fun s hs => h s (List.mem_cons_of_mem _ hs))
    refine Sym4.cons ?_ (ht.sym4.app (Sym4.cons (by simp [ALL]) this))
    split <;> simp [ALL]

theorem HP_split : ∀ (hs : List (List Nat)) (c : Nat), c < hs.length →
    ∃ Rest0 : List Nat, HP hs c = MP (hs.take c) ++ 3 :: Rest0 ∧ HP hs (c + 1) = MP (hs.take c) ++ 2 :: Rest0
  | [], c, h => by simp at h
  | [t], c, h => by
    have : c = 0 := by simp at h; omega
    subst this
    exact ⟨t, by simp [HP, MP], by simp [HP, MP]⟩
  | t :: u :: ts, 0, h => ⟨t ++ 1 :: HP (u :: ts) 0, by simp [HP, MP], by simp [HP, MP]⟩
  | t :: u :: ts, c + 1, h => by
    obtain ⟨R0, h1, h2⟩ := HP_split (u :: ts) c (by simp at h ⊢; omega)
    refine ⟨R0, ?_, ?_⟩
    · simp [HP, MP, h1]
    · simp [HP, MP, h2]

theorem HP_full : ∀ (hs : List (List Nat)), hs ≠ [] →
    ∃ tl, HP hs hs.length = MP hs.dropLast ++ 2 :: tl ∧ hs.getLast? = some tl
  | [], h => absurd rfl h
  | [t], _ => ⟨t, by simp [HP, MP], by simp⟩
  | t :: u :: ts, _ => by
    obtain ⟨tl, h1, h2⟩ := HP_full (u :: ts) (by simp)
    refine ⟨tl, ?_, ?_⟩
    · simp [HP, MP, h1]
      exact h1
    · simpa using h2

/-- Skip one `H` entry: walk to `H`, pass the passed entries, mark the first cell of the next one. -/
theorem hSkipG (P cb mb Rest0 : List Nat) (ws xs pasT : List (List Nat))
    (hcb : Bits cb) (hws : ∀ e ∈ ws, Bits e ∧ e ≠ []) (hmb : Bits mb) (hxs : ∀ e ∈ xs, Bits e ∧ e ≠ [])
    (hpas : ∀ t ∈ pasT, Bits t) (hP : Sym4 P) (hR : Sym4 Rest0) :
    zgiLogic.Reach
      (hdR QG.gN1 P (cb ++ 1 :: (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (MP pasT ++ 3 :: Rest0))))))
      (hd QG.gIL0 (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1] ++ MEs xs ++ [1] ++ MP pasT)
        (2 :: Rest0)) := by
  have sW := MEs_sym4 ws (fun e he => (hws e he).1)
  have sX := MEs_sym4 xs (fun e he => (hxs e he).1)
  have sP := MP_sym4 pasT hpas
  have s0 : Sym4 Rest0 := hR
  have s1 : Sym4 (MP pasT ++ 3 :: Rest0) := by simp [ALL, sP, s0]
  have s2 : Sym4 (MEs xs ++ 1 :: (MP pasT ++ 3 :: Rest0)) := by simp [ALL, sX, s1]
  have s3 : Sym4 (mb ++ 1 :: (MEs xs ++ 1 :: (MP pasT ++ 3 :: Rest0))) := by simp [ALL, hmb.sym4, s2]
  have s4 : Sym4 (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (MP pasT ++ 3 :: Rest0)))) := by simp [ALL, sW, s3]
  have hA := wn1Cells _ s4 cb P hcb hP
  have hB := wn1Walk _ s3 ws (P ++ cb ++ [1]) hws (by simp [ALL, hP, hcb.sym4])
  have hC := wn2Cells _ s2 mb (P ++ cb ++ [1] ++ MEs ws ++ [1]) hmb (by simp [ALL, hP, hcb.sym4, sW])
  have hD := wn2Walk _ s1 xs (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1]) hxs (by simp [ALL, hP, hcb.sym4, sW, hmb.sym4])
  have hE := s3Walk (3 :: Rest0) (by simp [ALL, s0]) pasT (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1] ++ MEs xs ++ [1]) hpas (by simp [ALL, hP, hcb.sym4, sW, hmb.sym4, sX])
  have hF := s3Mark (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1] ++ MEs xs ++ [1] ++ MP pasT) Rest0
    (by simp [ALL, hP, hcb.sym4, sW, hmb.sym4, sX, sP]) s0
  exact (hA.of_eq rfl rfl).trans ((hB.of_eq rfl rfl).trans ((hC.of_eq rfl rfl).trans ((hD.of_eq rfl rfl).trans
    ((hE.of_eq rfl rfl).trans (hF.of_eq rfl rfl)))))

theorem s4Walk (R : List Nat) (hR : Sym4 R) : ∀ (c P : List Nat), Bits c → Sym4 P →
    zgiLogic.Reach (hdR QG.gS4 P (c ++ R)) (hdR QG.gS4 (P ++ c) R)
  | [], P, _, _ => by simpa using (LTM.Reach.refl _ _)
  | b :: c, P, hc, hP => by
    have hb := hc b (List.mem_cons_self ..)
    have hc' : Bits c := fun a ha => hc a (List.mem_cons_of_mem _ ha)
    have h1 := s4Cell P (c ++ R) b hb hP (by simp [ALL, hR, hc'.sym4])
    have hP' : Sym4 (P ++ [b]) := by
      rcases mem_bits hb with rfl | rfl <;> simp [ALL, hP]
    have h2 := s4Walk R hR c (P ++ [b]) hc' hP'
    exact (h1.of_eq rfl rfl).trans (h2.of_eq rfl (by simp))

theorem s4Fail (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gS4 P (0 :: R)) (hd QG.gFG P (0 :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 0, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 0, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- A skip when every entry of `H` is already passed (the last one ends at the blank): failure. -/
theorem hSkipFail (P cb mb tl Z : List Nat) (ws xs pasT : List (List Nat))
    (hcb : Bits cb) (hws : ∀ e ∈ ws, Bits e ∧ e ≠ []) (hmb : Bits mb) (hxs : ∀ e ∈ xs, Bits e ∧ e ≠ [])
    (hpas : ∀ t ∈ pasT, Bits t) (htl : Bits tl) (hP : Sym4 P) (hZ : Sym4 Z) :
    zgiLogic.Reach
      (hdR QG.gN1 P (cb ++ 1 :: (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (MP pasT ++ 2 :: (tl ++ 0 :: Z)))))))
      (hd QG.gFG (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1] ++ MEs xs ++ [1] ++ MP pasT ++ [2] ++ tl)
        (0 :: Z)) := by
  have sW := MEs_sym4 ws (fun e he => (hws e he).1)
  have sX := MEs_sym4 xs (fun e he => (hxs e he).1)
  have sP := MP_sym4 pasT hpas
  have s0 : Sym4 (tl ++ 0 :: Z) := by simp [ALL, htl.sym4, hZ]
  have s1 : Sym4 (MP pasT ++ 2 :: (tl ++ 0 :: Z)) := by simp [ALL, sP, s0]
  have s2 : Sym4 (MEs xs ++ 1 :: (MP pasT ++ 2 :: (tl ++ 0 :: Z))) := by simp [ALL, sX, s1]
  have s3 : Sym4 (mb ++ 1 :: (MEs xs ++ 1 :: (MP pasT ++ 2 :: (tl ++ 0 :: Z)))) := by simp [ALL, hmb.sym4, s2]
  have s4 : Sym4 (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (MP pasT ++ 2 :: (tl ++ 0 :: Z))))) := by simp [ALL, sW, s3]
  have hA := wn1Cells _ s4 cb P hcb hP
  have hB := wn1Walk _ s3 ws (P ++ cb ++ [1]) hws (by simp [ALL, hP, hcb.sym4])
  have hC := wn2Cells _ s2 mb (P ++ cb ++ [1] ++ MEs ws ++ [1]) hmb (by simp [ALL, hP, hcb.sym4, sW])
  have hD := wn2Walk _ s1 xs (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1]) hxs (by simp [ALL, hP, hcb.sym4, sW, hmb.sym4])
  have hE := s3Walk (2 :: (tl ++ 0 :: Z)) (by simp [ALL, s0]) pasT (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1] ++ MEs xs ++ [1]) hpas (by simp [ALL, hP, hcb.sym4, sW, hmb.sym4, sX])
  have hF := s3Passed (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1] ++ MEs xs ++ [1] ++ MP pasT) (tl ++ 0 :: Z)
    (by simp [ALL, hP, hcb.sym4, sW, hmb.sym4, sX, sP]) s0
  have hG := s4Walk (0 :: Z) (by simp [ALL, hZ]) tl (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1] ++ MEs xs ++ [1] ++ MP pasT ++ [2]) htl
    (by simp [ALL, hP, hcb.sym4, sW, hmb.sym4, sX, sP])
  have hH := s4Fail (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1] ++ MEs xs ++ [1] ++ MP pasT ++ [2] ++ tl) Z
    (by simp [ALL, hP, hcb.sym4, sW, hmb.sym4, sX, sP, htl.sym4]) hZ
  exact (hA.of_eq rfl rfl).trans ((hB.of_eq rfl rfl).trans ((hC.of_eq rfl rfl).trans ((hD.of_eq rfl rfl).trans
    ((hE.of_eq rfl rfl).trans ((hF.of_eq rfl rfl).trans ((hG.of_eq rfl rfl).trans (hH.of_eq rfl rfl)))))))

/-- A family of tapes of the `H` region (nonzero part `Hc c`, then the blank and `Zt`),
indexed by the number `c` of passed entries. -/
structure HFam where
  Hc : Nat → List Nat
  N : Nat
  Zt : List Nat
  Hu : List Nat
  hZ : Sym4 Zt
  nb : ∀ c, c ≤ N → NoB (Hc c)
  un : ∀ c, c ≤ N → unm (Hc c) = Hu
  step : ∀ c, c < N → ∃ (pasT : List (List Nat)) (Rest0 : List Nat), (∀ t ∈ pasT, Bits t) ∧
    Hc c = MP pasT ++ 3 :: Rest0 ∧ Hc (c + 1) = MP pasT ++ 2 :: Rest0
  last : ∃ (pasT : List (List Nat)) (tl : List Nat), (∀ t ∈ pasT, Bits t) ∧ Bits tl ∧ Hc N = MP pasT ++ 2 :: tl

/-- Failure: the machine reaches the failure state on a marking of `U`. -/
def FailsTo (c : ZC) (U Z : List Nat) : Prop :=
  ∃ A R1 : List Nat, NoB A ∧ NoB R1 ∧ unm (A ++ R1) = U ∧ zgiLogic.Reach c (hdR QG.gFG A (R1 ++ 0 :: Z))

theorem gfgR (A0 : List Nat) (a : Nat) (R : List Nat) (ha : a ∈ NB) (hA : NoB A0) (hR : Sym4 R) :
    zgiLogic.Reach (hd QG.gFG (A0 ++ [a]) R) (hdR QG.gFG (A0 ++ [a]) R) := by
  have hV : Valid [ALL, ALL] [A0, R] := Valid.cons hA.sym4 (Valid.cons hR (Valid.nil _))
  simp [NB] at ha
  rcases ha with rfl | rfl | rfl
  · exact checkTF (env := [A0, R]) (E := []) (k := 3) hV trivial
      (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkTF (env := [A0, R]) (E := []) (k := 3) hV trivial
      (ls := [.blk 0 .id, .sym 2]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkTF (env := [A0, R]) (E := []) (k := 3) hV trivial
      (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- From the head on the last cell: step right. -/
theorem gfgR' (A R : List Nat) (hA : NoB A) (hne : A ≠ []) (hR : Sym4 R) :
    zgiLogic.Reach (hd QG.gFG A R) (hdR QG.gFG A R) := by
  obtain ⟨A0, a, hA0⟩ := List.eq_nil_or_concat A |>.resolve_left hne
  rw [List.concat_eq_append] at hA0
  subst hA0
  exact gfgR A0 a R (hA a (by simp)) (fun x hx => hA x (by simp [hx])) hR

theorem HFam.sym (F : HFam) (c : Nat) (hc : c ≤ F.N) : Sym4 (F.Hc c ++ 0 :: F.Zt) :=
  (F.nb c hc).sym4.app (Sym4.cons (by simp [ALL]) F.hZ)

/-- The inner loop over a family of `H` tapes: `n` passes starting from `c` passed entries. -/
theorem innerLoopU (F : HFam) (q : Nat) (hq : q = QG.gIL1b ∨ q = QG.gIL1) (ms : List Nat) (ws xs : List (List Nat))
    (mb : List Nat) (hms : ∀ e ∈ ms, 1 ≤ e) (hws : ∀ e ∈ ws, Bits e ∧ e ≠ []) (hmb : Bits mb)
    (hxs : ∀ e ∈ xs, Bits e ∧ e ≠ []) :
    ∀ (n i c : Nat), c + n ≤ F.N →
    zgiLogic.Reach
      (hdR q (MEnc ms) (List.replicate i 2 ++ List.replicate (n + 1) 3 ++ 1 ::
        (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (F.Hc c ++ 0 :: F.Zt))))))
      (hdR QG.gD1 (MEnc ms ++ List.replicate (i + n) 2 ++ [3])
        (1 :: (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (F.Hc (c + n) ++ 0 :: F.Zt)))))) := by
  intro n
  induction n generalizing q with
  | zero =>
    intro i c hc
    have sW := MEs_sym4 ws (fun e he => (hws e he).1)
    have sX := MEs_sym4 xs (fun e he => (hxs e he).1)
    have sH := F.sym c (by omega)
    have hM := ilMark q hq (MEnc ms) (1 :: (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (F.Hc c ++ 0 :: F.Zt))))) i
      (by simp [ALL]) (by simp [ALL, sW, hmb.sym4, sX, sH])
    have hE := ilpEnd (MEnc ms ++ List.replicate (i + 1) 2) (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (F.Hc c ++ 0 :: F.Zt))))
      (by simp [ALL]) (by simp [ALL, sW, hmb.sym4, sX, sH])
    have hU := iluStep (MEnc ms ++ List.replicate i 2) (1 :: (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (F.Hc c ++ 0 :: F.Zt)))))
      (by simp [ALL]) (by simp [ALL, sW, hmb.sym4, sX, sH])
    have e1 : MEnc ms ++ List.replicate (i + 1) 2 = MEnc ms ++ List.replicate i 2 ++ [2] := by
      simp [List.replicate_succ', List.append_assoc]
    rw [← e1] at hU
    simpa [List.append_assoc] using hM.trans (hE.trans hU)
  | succ n ih =>
    intro i c hc
    obtain ⟨pasT, Rest0, hp, h1, h2⟩ := F.step c (by omega)
    have sW := MEs_sym4 ws (fun e he => (hws e he).1)
    have sX := MEs_sym4 xs (fun e he => (hxs e he).1)
    have sP := MP_sym4 pasT hp
    have sH := F.sym c (by omega)
    have sH1 := F.sym (c + 1) (by omega)
    have sR0 : Sym4 (Rest0 ++ 0 :: F.Zt) := by
      have := sH
      rw [h1] at this
      simp [ALL] at this
      simp [ALL, this.2.1, this.2.2]
    have hM := ilMark q hq (MEnc ms) (List.replicate (n + 1) 3 ++ 1 :: (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (F.Hc c ++ 0 :: F.Zt))))) i
      (by simp [ALL]) (by simp [ALL, sW, hmb.sym4, sX, sH])
    have hMore := ilpMore (MEnc ms ++ List.replicate (i + 1) 2) (List.replicate n 3 ++ 1 :: (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (F.Hc c ++ 0 :: F.Zt)))))
      (by simp [ALL]) (by simp [ALL, sW, hmb.sym4, sX, sH])
    have hSk := hSkipG (MEnc ms ++ List.replicate (i + 1) 2 ++ [3]) (List.replicate n 3) mb (Rest0 ++ 0 :: F.Zt) ws xs pasT
      (bits_rep3 n) hws hmb hxs hp (by simp [ALL]) sR0
    have hW := il0Walk' (MEnc ms ++ List.replicate (i + 1) 2 ++ [3] ++ List.replicate n 3 ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1] ++ MEs xs ++ [1] ++ MP pasT)
      (2 :: (Rest0 ++ 0 :: F.Zt))
      (by
        have := MEs_noB ws (fun e he => (hws e he).1)
        have := MEs_noB xs (fun e he => (hxs e he).1)
        have := MP_noB pasT hp
        simp [NB, *, hmb.noB])
      (by simp [ALL, sR0])
    have hS2 := ilSkipList (List.replicate (i + 1) 2 ++ List.replicate (n + 1) 3 ++ 1 :: (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (F.Hc (c + 1) ++ 0 :: F.Zt)))))
      (by simp [ALL, sW, hmb.sym4, sX, sH1]) ms [] hms (by simp [ALL])
    have hI := hS2.trans (ih QG.gIL1b (Or.inl rfl) (i + 1) (c + 1) (by omega))
    refine ((hM.of_eq (by simp [List.replicate_succ, h1]) rfl).trans ((hMore.of_eq (by simp [List.replicate_succ, h1]) rfl).trans
      ((hSk.of_eq (by simp [h1, List.append_assoc]) rfl).trans ((hW.of_eq rfl rfl).trans (hI.of_eq ?_ ?_)))))
    · simp [h2, List.replicate_succ, List.append_assoc]
    · simp [Nat.add_assoc, Nat.add_comm 1 n]

theorem FailsTo.pre {c1 c2 : ZC} {U Z : List Nat} (h : zgiLogic.Reach c1 c2) (hf : FailsTo c2 U Z) : FailsTo c1 U Z := by
  obtain ⟨A, R1, hA, hR, hu, hr⟩ := hf
  exact ⟨A, R1, hA, hR, hu, h.trans hr⟩

theorem FailsTo.cast {c : ZC} {U U' Z : List Nat} (e : U = U') (hf : FailsTo c U Z) : FailsTo c U' Z := e ▸ hf

theorem FailsTo.of_hd {c : ZC} {A : List Nat} {U Z : List Nat} (hA : NoB A) (hne : A ≠ []) (hZ : Sym4 Z)
    (hu : unm A = U) (h : zgiLogic.Reach c (hd QG.gFG A (0 :: Z))) : FailsTo c U Z :=
  ⟨A, [], hA, NoB.nil, by simpa using hu, by
    simpa using h.trans (gfgR' A (0 :: Z) hA hne (by simp [ALL, hZ]))⟩

theorem unm_unm (A : List Nat) : unm (unm A) = unm A := by
  induction A with
  | nil => rfl
  | cons a l ih => simp only [unm_cons, ih]; congr 1; unfold unm1; split <;> simp_all

theorem unm_rep2' (k : Nat) : unm (List.replicate k 2) = List.replicate k 3 := unm_rep2 k

/-- Failure of the inner loop: not enough entries in `H`. -/
theorem innerLoopF (F : HFam) (q : Nat) (hq : q = QG.gIL1b ∨ q = QG.gIL1) (ms : List Nat) (ws xs : List (List Nat))
    (mb : List Nat) (hms : ∀ e ∈ ms, 1 ≤ e) (hws : ∀ e ∈ ws, Bits e ∧ e ≠ []) (hmb : Bits mb)
    (hxs : ∀ e ∈ xs, Bits e ∧ e ≠ []) :
    ∀ (n i c : Nat), c ≤ F.N → F.N < c + n →
    FailsTo
      (hdR q (MEnc ms) (List.replicate i 2 ++ List.replicate (n + 1) 3 ++ 1 ::
        (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (F.Hc c ++ 0 :: F.Zt))))))
      (unm (MEnc ms ++ List.replicate i 2 ++ List.replicate (n + 1) 3 ++ 1 ::
        (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: F.Hu))))) F.Zt := by
  intro n
  induction n generalizing q with
  | zero => intro i c h1 h2; omega
  | succ n ih =>
    intro i c hc1 hc2
    have sW := MEs_sym4 ws (fun e he => (hws e he).1)
    have sX := MEs_sym4 xs (fun e he => (hxs e he).1)
    have sH := F.sym c hc1
    by_cases hlt : c < F.N
    · obtain ⟨pasT, Rest0, hp, h1, h2⟩ := F.step c hlt
      have sP := MP_sym4 pasT hp
      have sH1 := F.sym (c + 1) (by omega)
      have sR0 : Sym4 (Rest0 ++ 0 :: F.Zt) := by
        have := sH
        rw [h1] at this
        simp [ALL] at this
        simp [ALL, this.2.1, this.2.2]
      have hM := ilMark q hq (MEnc ms) (List.replicate (n + 1) 3 ++ 1 :: (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (F.Hc c ++ 0 :: F.Zt))))) i
        (by simp [ALL]) (by simp [ALL, sW, hmb.sym4, sX, sH])
      have hMore := ilpMore (MEnc ms ++ List.replicate (i + 1) 2) (List.replicate n 3 ++ 1 :: (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (F.Hc c ++ 0 :: F.Zt)))))
        (by simp [ALL]) (by simp [ALL, sW, hmb.sym4, sX, sH])
      have hSk := hSkipG (MEnc ms ++ List.replicate (i + 1) 2 ++ [3]) (List.replicate n 3) mb (Rest0 ++ 0 :: F.Zt) ws xs pasT
        (bits_rep3 n) hws hmb hxs hp (by simp [ALL]) sR0
      have hW := il0Walk' (MEnc ms ++ List.replicate (i + 1) 2 ++ [3] ++ List.replicate n 3 ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1] ++ MEs xs ++ [1] ++ MP pasT)
        (2 :: (Rest0 ++ 0 :: F.Zt))
        (by
          have := MEs_noB ws (fun e he => (hws e he).1)
          have := MEs_noB xs (fun e he => (hxs e he).1)
          have := MP_noB pasT hp
          simp [NB, *, hmb.noB])
        (by simp [ALL, sR0])
      have hS2 := ilSkipList (List.replicate (i + 1) 2 ++ List.replicate (n + 1) 3 ++ 1 :: (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (F.Hc (c + 1) ++ 0 :: F.Zt)))))
        (by simp [ALL, sW, hmb.sym4, sX, sH1]) ms [] hms (by simp [ALL])
      have hI := ih QG.gIL1b (Or.inl rfl) (i + 1) (c + 1) (by omega) (by omega)
      refine FailsTo.pre (c2 := hdR QG.gIL1b (MEnc ms) (List.replicate (i + 1) 2 ++ List.replicate (n + 1) 3 ++ 1 ::
        (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (F.Hc (c + 1) ++ 0 :: F.Zt)))))) ?_ (FailsTo.cast ?_ hI)
      · exact (((hM.of_eq (by simp [List.replicate_succ, h1]) rfl).trans ((hMore.of_eq (by simp [List.replicate_succ, h1]) rfl).trans
          ((hSk.of_eq (by simp [h1, List.append_assoc]) rfl).trans (hW.of_eq rfl rfl)))).of_eq rfl
            (by simp [h2, List.replicate_succ, List.append_assoc])).trans hS2
      · simp [unm_append, unm_rep2, unm_rep3, unm1, List.replicate_succ', List.append_assoc, rep_cons_comm]
    · have hcN : c = F.N := by omega
      obtain ⟨pasT, tl, hp, htl, hN0⟩ := F.last
      have hN : F.Hc c = MP pasT ++ 2 :: tl := by rw [hcN]; exact hN0
      have sP := MP_sym4 pasT hp
      have hZ := F.hZ
      have hM := ilMark q hq (MEnc ms) (List.replicate (n + 1) 3 ++ 1 :: (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (F.Hc c ++ 0 :: F.Zt))))) i
        (by simp [ALL]) (by simp [ALL, sW, hmb.sym4, sX, sH])
      have hMore := ilpMore (MEnc ms ++ List.replicate (i + 1) 2) (List.replicate n 3 ++ 1 :: (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (F.Hc c ++ 0 :: F.Zt)))))
        (by simp [ALL]) (by simp [ALL, sW, hmb.sym4, sX, sH])
      have hSk := hSkipFail (MEnc ms ++ List.replicate (i + 1) 2 ++ [3]) (List.replicate n 3) mb tl F.Zt ws xs pasT
        (bits_rep3 n) hws hmb hxs hp htl (by simp [ALL]) hZ
      have hun := F.un c hc1
      rw [hN] at hun
      refine FailsTo.of_hd (A := MEnc ms ++ List.replicate (i + 1) 2 ++ [3] ++ List.replicate n 3 ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1] ++ MEs xs ++ [1] ++ MP pasT ++ [2] ++ tl) ?_ ?_ hZ ?_
        (((hM.of_eq (by simp [List.replicate_succ, hN]) rfl).trans ((hMore.of_eq (by simp [List.replicate_succ, hN]) rfl).trans
          (hSk.of_eq (by simp [hN, List.append_assoc]) rfl))))
      · have := MEs_noB ws (fun e he => (hws e he).1)
        have := MEs_noB xs (fun e he => (hxs e he).1)
        have := MP_noB pasT hp
        simp [NB, *, hmb.noB, htl.noB]
      · simp
      · rw [← hun]
        simp [unm_append, unm_rep2, unm_rep3, unm1, List.replicate_succ', List.append_assoc, rep_cons_comm, unm_unm]

end ZP.G
