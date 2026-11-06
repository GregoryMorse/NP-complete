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

/-- The shape of what follows the last `H` entry: nothing, one `M`, or `M M` and more tape. -/
def JShape (J : List Nat) : Prop := NoB J ∧ (J = [] ∨ J = [1] ∨ ∃ J', J = 1 :: 1 :: J')

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
  last : ∃ (pasT : List (List Nat)) (tl J : List Nat), (∀ t ∈ pasT, Bits t) ∧ Bits tl ∧ JShape J ∧ Hc N = MP pasT ++ 2 :: (tl ++ J)

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

theorem FailsTo.ofCfg {c c' : ZC} {U Z : List Nat} (e : c = c') (hf : FailsTo c' U Z) : FailsTo c U Z := e ▸ hf

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

theorem s3FailB (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gS3 P (0 :: R)) (hd QG.gFG P (0 :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 0, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 0, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem FailsTo.mk' {c : ZC} {A R1 Z L : List Nat} (hA : NoB A) (hR : NoB R1) (hL : A ++ R1 = L)
    (h : zgiLogic.Reach c (hdR QG.gFG A (R1 ++ 0 :: Z))) : FailsTo c (unm L) Z :=
  ⟨A, R1, hA, hR, by rw [hL], h⟩

/-- A skip when every entry of `H` is already passed (the last one is followed by `J`, then the blank): failure. -/
theorem hSkipFail (P cb mb tl J Z : List Nat) (ws xs pasT : List (List Nat))
    (hcb : Bits cb) (hws : ∀ e ∈ ws, Bits e ∧ e ≠ []) (hmb : Bits mb) (hxs : ∀ e ∈ xs, Bits e ∧ e ≠ [])
    (hpas : ∀ t ∈ pasT, Bits t) (htl : Bits tl) (hJ : JShape J) (hP : Sym4 P) (hPn : NoB P) (hZ : Sym4 Z) :
    FailsTo
      (hdR QG.gN1 P (cb ++ 1 :: (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (MP pasT ++ 2 :: (tl ++ J ++ 0 :: Z)))))))
      (unm (P ++ cb ++ 1 :: (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (MP pasT ++ 2 :: (tl ++ J)))))))
      Z := by
  have sW := MEs_sym4 ws (fun e he => (hws e he).1)
  have sX := MEs_sym4 xs (fun e he => (hxs e he).1)
  have sP := MP_sym4 pasT hpas
  have sJ : Sym4 J := hJ.1.sym4
  have s0 : Sym4 (tl ++ J ++ 0 :: Z) := (htl.sym4.app sJ).app (Sym4.cons (by simp [ALL]) hZ)
  have s1 : Sym4 (MP pasT ++ 2 :: (tl ++ J ++ 0 :: Z)) := sP.app (Sym4.cons (by simp [ALL]) s0)
  have s2 : Sym4 (MEs xs ++ 1 :: (MP pasT ++ 2 :: (tl ++ J ++ 0 :: Z))) := sX.app (Sym4.cons (by simp [ALL]) s1)
  have s3 : Sym4 (mb ++ 1 :: (MEs xs ++ 1 :: (MP pasT ++ 2 :: (tl ++ J ++ 0 :: Z)))) := hmb.sym4.app (Sym4.cons (by simp [ALL]) s2)
  have s4 : Sym4 (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (MP pasT ++ 2 :: (tl ++ J ++ 0 :: Z))))) := sW.app (Sym4.cons (by simp [ALL]) s3)
  have hA := wn1Cells _ s4 cb P hcb hP
  have hB := wn1Walk _ s3 ws (P ++ cb ++ [1]) hws (by simp [ALL, hP, hcb.sym4])
  have hC := wn2Cells _ s2 mb (P ++ cb ++ [1] ++ MEs ws ++ [1]) hmb (by simp [ALL, hP, hcb.sym4, sW])
  have hD := wn2Walk _ s1 xs (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1]) hxs (by simp [ALL, hP, hcb.sym4, sW, hmb.sym4])
  have hE := s3Walk (2 :: (tl ++ J ++ 0 :: Z)) (Sym4.cons (by simp [ALL]) s0) pasT (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1] ++ MEs xs ++ [1]) hpas (by simp [ALL, hP, hcb.sym4, sW, hmb.sym4, sX])
  have hF := s3Passed (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1] ++ MEs xs ++ [1] ++ MP pasT) (tl ++ J ++ 0 :: Z)
    (by simp [ALL, hP, hcb.sym4, sW, hmb.sym4, sX, sP]) s0
  have sPP : Sym4 (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1] ++ MEs xs ++ [1] ++ MP pasT ++ [2]) := by
    simp [ALL, hP, hcb.sym4, sW, hmb.sym4, sX, sP]
  have hG := s4Walk (J ++ 0 :: Z) (sJ.app (Sym4.cons (by simp [ALL]) hZ)) tl (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1] ++ MEs xs ++ [1] ++ MP pasT ++ [2]) htl sPP
  have hpre := (hA.of_eq rfl rfl).trans ((hB.of_eq rfl rfl).trans ((hC.of_eq rfl rfl).trans ((hD.of_eq rfl rfl).trans
    ((hE.of_eq rfl rfl).trans ((hF.of_eq rfl rfl).trans (hG.of_eq (by simp [List.append_assoc]) rfl))))))
  have nbL : NoB (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1] ++ MEs xs ++ [1] ++ MP pasT ++ [2] ++ tl) := by
    have h1 := MEs_noB ws (fun e he => (hws e he).1)
    have h2 := MEs_noB xs (fun e he => (hxs e he).1)
    have h3 := MP_noB pasT hpas
    simp [NB, hPn, hcb.noB, h1, hmb.noB, h2, h3, htl.noB]
  have sL : Sym4 (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1] ++ MEs xs ++ [1] ++ MP pasT ++ [2] ++ tl) := nbL.sym4
  have hne : (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1] ++ MEs xs ++ [1] ++ MP pasT ++ [2] ++ tl) ≠ [] := by simp
  have nbM : NoB [1] := by simp [NB]
  have nb1 := nbL.app nbM
  have nb2 := nb1.app nbM
  rcases hJ.2 with hJ0 | hJ1 | ⟨J', hJ'⟩
  · subst hJ0
    have hH := s4Fail _ Z sL hZ
    refine FailsTo.mk' nbL NoB.nil (by simp [List.append_assoc]) ?_
    exact (hpre.trans hH).trans (gfgR' _ _ nbL hne (by simp [ALL, hZ]))
  · subst hJ1
    have h1 := s4End _ (0 :: Z) sL (Sym4.cons (by simp [ALL]) hZ)
    have h2 := s3FailB _ Z nb1.sym4 hZ
    refine FailsTo.mk' nb1 NoB.nil (by simp [List.append_assoc]) ?_
    exact ((hpre.trans h1).trans h2).trans (gfgR' _ _ nb1 (by simp) (Sym4.cons (by simp [ALL]) hZ))
  · subst hJ'
    have hJn : NoB J' := by
      have := hJ.1
      simp only [NoB_cons_iff] at this
      exact this.2.2
    have sR : Sym4 (J' ++ 0 :: Z) := hJn.sym4.app (Sym4.cons (by simp [ALL]) hZ)
    have h1 := s4End _ (1 :: (J' ++ 0 :: Z)) sL (Sym4.cons (by simp [ALL]) sR)
    have h2 := s3Fail _ (J' ++ 0 :: Z) nb1.sym4 sR
    refine FailsTo.mk' nb2 hJn (by simp [List.append_assoc]) ?_
    exact (hpre.trans h1).trans h2

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
      obtain ⟨pasT, tl, J, hp, htl, hJ, hN0⟩ := F.last
      have hN : F.Hc c = MP pasT ++ 2 :: (tl ++ J) := by rw [hcN]; exact hN0
      have hZ := F.hZ
      have hM := ilMark q hq (MEnc ms) (List.replicate (n + 1) 3 ++ 1 :: (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (F.Hc c ++ 0 :: F.Zt))))) i
        (by simp [ALL]) (by simp [ALL, sW, hmb.sym4, sX, sH])
      have hMore := ilpMore (MEnc ms ++ List.replicate (i + 1) 2) (List.replicate n 3 ++ 1 :: (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (F.Hc c ++ 0 :: F.Zt)))))
        (by simp [ALL]) (by simp [ALL, sW, hmb.sym4, sX, sH])
      have hSk := hSkipFail (MEnc ms ++ List.replicate (i + 1) 2 ++ [3]) (List.replicate n 3) mb tl J F.Zt ws xs pasT
        (bits_rep3 n) hws hmb hxs hp htl hJ (by simp [ALL, MEnc_sym4]) (by simp [MEnc_nb, NB]) hZ
      have hun := F.un c hc1
      rw [hN] at hun
      refine FailsTo.pre ((hM.of_eq (by simp [List.replicate_succ, hN]) rfl).trans (hMore.of_eq (by simp [List.replicate_succ, hN]) rfl))
        (FailsTo.ofCfg ?_ (FailsTo.cast ?_ hSk))
      · simp [hN, List.append_assoc]
      · rw [← hun]
        simp [unm_append, unm_rep2, unm_rep3, unm1, List.replicate_succ', List.append_assoc, rep_cons_comm, unm_unm]


theorem HP_noB : ∀ (hs : List (List Nat)) (c : Nat), (∀ t ∈ hs, Bits t) → NoB (HP hs c)
  | [], _, _ => NoB.nil
  | [t], c, h => by
    have ht := (h t (List.mem_cons_self ..)).noB
    intro a ha
    simp only [HP, List.mem_cons] at ha
    rcases ha with rfl | ha
    · split <;> simp [NB]
    · exact ht a ha
  | t :: u :: ts, c, h => by
    have ht := (h t (List.mem_cons_self ..)).noB
    have ih := HP_noB (u :: ts) (c - 1) (fun s hs => h s (List.mem_cons_of_mem _ hs))
    intro a ha
    simp only [HP, List.mem_cons, List.mem_append] at ha
    rcases ha with rfl | ha | rfl | ha
    · split <;> simp [NB]
    · exact ht a ha
    · simp [NB]
    · exact ih a ha

theorem HP_unm : ∀ (hs : List (List Nat)) (c : Nat), unm (HP hs c) = unm (HP hs 0)
  | [], _ => rfl
  | [t], c => by
    simp only [HP]; split <;> simp [unm_cons, unm1]
  | t :: u :: ts, c => by
    have ih := HP_unm (u :: ts) (c - 1)
    have ih0 := HP_unm (u :: ts) (0 - 1)
    simp only [HP, unm_cons, unm_append, ih, ih0]
    split <;> simp [unm1]

/-- The family of `H` tapes with `c` passed entries, `c = 0..|hs|`, followed by `J`. -/
def HFam.ofHP (hs : List (List Nat)) (hne : hs ≠ []) (hb : ∀ t ∈ hs, Bits t) (J : List Nat) (hJ : JShape J)
    (Zt : List Nat) (hZ : Sym4 Zt) : HFam where
  Hc := fun c => HP hs c ++ J
  N := hs.length
  Zt := Zt
  Hu := unm (HP hs 0 ++ J)
  hZ := hZ
  nb := fun c _ => (HP_noB hs c hb).app hJ.1
  un := fun c _ => by rw [unm_append, unm_append, HP_unm hs c]
  step := fun c hc => by
    obtain ⟨R0, h1, h2⟩ := HP_split hs c hc
    refine ⟨hs.take c, R0 ++ J, fun t ht => hb t (List.mem_of_mem_take ht), by simp [h1], by simp [h2]⟩
  last := by
    obtain ⟨tl, h1, h2⟩ := HP_full hs hne
    refine ⟨hs.dropLast, tl, J, fun t ht => hb t (List.dropLast_subset _ ht), hb tl (List.mem_of_getLast? h2), hJ, by simp [h1]⟩


theorem HFam.hu_unm (F : HFam) : unm F.Hu = F.Hu := by
  rw [← F.un 0 (Nat.zero_le _), unm_unm]

/-- The unmarked content of the check tape (the target `nn+1` cells, `m` cells of `m`). -/
def UG (ms : List Nat) (ws xs : List (List Nat)) (nn m : Nat) (Hu : List Nat) : List Nat :=
  Enc ms ++ List.replicate (nn + 1) 3 ++ 1 :: (unm (MEs ws) ++ 1 :: (List.replicate m 3 ++ 1 :: (unm (MEs xs) ++ 1 :: Hu)))

/-- A row iteration that runs out of `H`. -/
theorem rowIterF (F : HFam) (ms : List Nat) (ws xs : List (List Nat))
    (hms : ∀ e ∈ ms, 1 ≤ e) (hws : ∀ e ∈ ws, Bits e ∧ e ≠ []) (hxs : ∀ e ∈ xs, Bits e ∧ e ≠ [])
    (i n p q c : Nat) (hc : c ≤ F.N) (hn : F.N < c + (i + n)) :
    FailsTo
      (hd QG.gTR1 (MEnc ms ++ List.replicate i 2 ++ 3 :: (List.replicate n 3 ++ 1 :: (MEs ws ++ 1 :: List.replicate p 3)))
        (2 :: (List.replicate q 2 ++ 1 :: (MEs xs ++ 1 :: (F.Hc c ++ 0 :: F.Zt)))))
      (UG ms ws xs (i + n) (p + q + 1) F.Hu) F.Zt := by
  have sX := MEs_sym4 xs (fun e he => (hxs e he).1)
  have sH := F.sym c hc
  have hQ : NoB (List.replicate n 3 ++ 1 :: (MEs ws ++ 1 :: List.replicate p 3)) := by
    have := MEs_noB ws (fun e he => (hws e he).1)
    simp [NB, this]
  have hR' : Sym4 (List.replicate q 2 ++ 1 :: (MEs xs ++ 1 :: (F.Hc c ++ 0 :: F.Zt))) :=
    (rep_sym4 q 2 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) (sX.app (Sym4.cons (by simp [ALL]) sH)))
  have h1 := rowReset ms hms i _ _ hQ hR'
  have hmb : Bits (List.replicate p 3 ++ List.replicate (q + 1) 2) := bits_app (bits_rep3 p) (bits_rep2 (q + 1))
  have h2 := innerLoopF F QG.gIL1 (Or.inr rfl) ms ws xs _ hms hws hmb hxs (i + n) 0 c hc hn
  have e1 : List.replicate i 3 ++ 3 :: (List.replicate n 3 ++ 1 :: (MEs ws ++ 1 :: List.replicate p 3) ++ 2 :: (List.replicate q 2 ++ 1 :: (MEs xs ++ 1 :: (F.Hc c ++ 0 :: F.Zt))))
      = List.replicate 0 2 ++ List.replicate (i + n + 1) 3 ++ 1 ::
        (MEs ws ++ 1 :: ((List.replicate p 3 ++ List.replicate (q + 1) 2) ++ 1 :: (MEs xs ++ 1 :: (F.Hc c ++ 0 :: F.Zt)))) := by
    have : List.replicate (i + n + 1) 3 = List.replicate i 3 ++ 3 :: List.replicate n 3 := by
      rw [show i + n + 1 = i + (n + 1) from rfl, ← List.replicate_append_replicate, List.replicate_succ]
    rw [this]
    simp [List.replicate_succ, List.append_assoc]
  refine FailsTo.pre (h1.of_eq rfl (by rw [e1])) (FailsTo.cast ?_ h2)
  have e2 : List.replicate (p + q + 1) 3 = List.replicate p 3 ++ List.replicate (q + 1) 3 := by
    rw [show p + q + 1 = p + (q + 1) from by omega, ← List.replicate_append_replicate]
  simp only [UG, e2, unm_append, unm_rep2, unm_rep3, unm_MEnc, unm_cons, unm1, List.replicate_zero, List.nil_append,
    List.append_assoc, List.cons_append]
  simp [unm1, F.hu_unm]

/-- One row iteration over an `H`-family (success). -/
theorem rowIterU (F : HFam) (ms : List Nat) (ws xs : List (List Nat))
    (hms : ∀ e ∈ ms, 1 ≤ e) (hws : ∀ e ∈ ws, Bits e ∧ e ≠ []) (hxs : ∀ e ∈ xs, Bits e ∧ e ≠ [])
    (i n p q c : Nat) (hn : c + (i + n) ≤ F.N) :
    zgiLogic.Reach
      (hd QG.gTR1 (MEnc ms ++ List.replicate i 2 ++ 3 :: (List.replicate n 3 ++ 1 :: (MEs ws ++ 1 :: List.replicate p 3)))
        (2 :: (List.replicate q 2 ++ 1 :: (MEs xs ++ 1 :: (F.Hc c ++ 0 :: F.Zt)))))
      (hdR QG.gD2 (MEnc ms ++ List.replicate (i + n) 2 ++ [3] ++ 1 :: (MEs ws ++ [1]))
        (List.replicate p 3 ++ (List.replicate (q + 1) 2 ++ 1 :: (MEs xs ++ 1 :: (F.Hc (c + (i + n)) ++ 0 :: F.Zt))))) := by
  have sW := MEs_sym4 ws (fun e he => (hws e he).1)
  have sX := MEs_sym4 xs (fun e he => (hxs e he).1)
  have sH := F.sym c (by omega)
  have sH' := F.sym (c + (i + n)) hn
  have hQ : NoB (List.replicate n 3 ++ 1 :: (MEs ws ++ 1 :: List.replicate p 3)) := by
    have := MEs_noB ws (fun e he => (hws e he).1)
    simp [NB, this]
  have hR' : Sym4 (List.replicate q 2 ++ 1 :: (MEs xs ++ 1 :: (F.Hc c ++ 0 :: F.Zt))) := by
    simp [ALL, sX, sH, rep_sym4 q 2 (by simp [ALL])]
  have h1 := rowReset ms hms i _ _ hQ hR'
  have hmb : Bits (List.replicate p 3 ++ List.replicate (q + 1) 2) := bits_app (bits_rep3 p) (bits_rep2 (q + 1))
  have h2 := innerLoopU F QG.gIL1 (Or.inr rfl) ms ws xs _ hms hws hmb hxs (i + n) 0 c hn
  have sMb : Sym4 (List.replicate p 3 ++ List.replicate (q + 1) 2) := hmb.sym4
  have sR2 : Sym4 ((List.replicate p 3 ++ List.replicate (q + 1) 2) ++ 1 :: (MEs xs ++ 1 ::
      (F.Hc (c + (i + n)) ++ 0 :: F.Zt))) :=
    sMb.app (Sym4.cons (by simp [ALL]) (sX.app (Sym4.cons (by simp [ALL]) sH')))
  have sP0 : Sym4 (MEnc ms ++ List.replicate (0 + (i + n)) 2 ++ [3]) :=
    ((MEnc_sym4 ms).app (Sym4.rep _ _ (by simp [ALL]))).app (by simp [ALL])
  have sRh : Sym4 (MEs ws ++ 1 :: ((List.replicate p 3 ++ List.replicate (q + 1) 2) ++ 1 :: (MEs xs ++ 1 ::
      (F.Hc (c + (i + n)) ++ 0 :: F.Zt)))) :=
    sW.app (Sym4.cons (by simp [ALL]) sR2)
  have h3 := wd1EndIn (MEnc ms ++ List.replicate (0 + (i + n)) 2 ++ [3])
    (MEs ws ++ 1 :: ((List.replicate p 3 ++ List.replicate (q + 1) 2) ++ 1 :: (MEs xs ++ 1 ::
      (F.Hc (c + (i + n)) ++ 0 :: F.Zt)))) sP0 sRh
  have h4 := wd1Walk _ sR2 ws (MEnc ms ++ List.replicate (0 + (i + n)) 2 ++ [3] ++ [1]) hws (sP0.app (by simp [ALL]))
  have e1 : List.replicate i 3 ++ 3 :: (List.replicate n 3 ++ 1 :: (MEs ws ++ 1 :: List.replicate p 3) ++ 2 :: (List.replicate q 2 ++ 1 :: (MEs xs ++ 1 :: (F.Hc c ++ 0 :: F.Zt))))
      = List.replicate 0 2 ++ List.replicate (i + n + 1) 3 ++ 1 ::
        (MEs ws ++ 1 :: ((List.replicate p 3 ++ List.replicate (q + 1) 2) ++ 1 :: (MEs xs ++ 1 :: (F.Hc c ++ 0 :: F.Zt)))) := by
    have : List.replicate (i + n + 1) 3 = List.replicate i 3 ++ 3 :: List.replicate n 3 := by
      rw [show i + n + 1 = i + (n + 1) from rfl, ← List.replicate_append_replicate, List.replicate_succ]
    rw [this]
    simp [List.replicate_succ, List.append_assoc]
  exact (((h1.of_eq rfl (by rw [e1])).trans h2).trans h3).trans (h4.of_eq rfl (by simp [List.append_assoc]))


/-- The whole row part over an `H`-family. -/
theorem rowLoopU (F : HFam) (ms : List Nat) (ws xs : List (List Nat))
    (hms : ∀ e ∈ ms, 1 ≤ e) (hws : ∀ e ∈ ws, Bits e ∧ e ≠ []) (hxs : ∀ e ∈ xs, Bits e ∧ e ≠ [])
    (nn : Nat) : ∀ (p i n q c : Nat), i + n = nn → c + (p + 1) * nn ≤ F.N →
    zgiLogic.Reach
      (hd QG.gTR1 (MEnc ms ++ List.replicate i 2 ++ 3 :: (List.replicate n 3 ++ 1 :: (MEs ws ++ 1 :: List.replicate p 3)))
        (2 :: (List.replicate q 2 ++ 1 :: (MEs xs ++ 1 :: (F.Hc c ++ 0 :: F.Zt)))))
      (hd QG.gGL (MEnc ms ++ List.replicate nn 2 ++ 3 :: 1 :: MEs ws)
        (1 :: (List.replicate (p + q + 1) 2 ++ 1 :: (MEs xs ++ 1 :: (F.Hc (c + (p + 1) * nn) ++ 0 :: F.Zt))))) := by
  intro p
  induction p with
  | zero =>
    intro i n q c hin hc
    subst hin
    have h1 := rowIterU F ms ws xs hms hws hxs i n 0 q c (by simpa using hc)
    have sX := MEs_sym4 xs (fun e he => (hxs e he).1)
    have sH' := F.sym (c + (i + n)) (by simpa using hc)
    have hS : Sym4 (MEs xs ++ 1 :: (F.Hc (c + (i + n)) ++ 0 :: F.Zt)) :=
      sX.app (Sym4.cons (by simp [ALL]) sH')
    have hP : Sym4 (MEnc ms ++ List.replicate (i + n) 2 ++ [3] ++ 1 :: (MEs ws ++ [1])) := by
      have sW := MEs_sym4 ws (fun e he => (hws e he).1)
      exact (((MEnc_sym4 ms).app (Sym4.rep _ _ (by simp [ALL]))).app (by simp [ALL])).app
        (Sym4.cons (by simp [ALL]) (sW.app (by simp [ALL])))
    have h2 := (gd2Row _ hS q 0 _ hP).2 (MEnc ms ++ List.replicate (i + n) 2 ++ [3] ++ 1 :: MEs ws) rfl (by simp)
    simp only [List.replicate, List.nil_append] at h1
    have := h1.trans h2
    simpa [Nat.zero_add, Nat.one_mul, List.append_assoc] using this
  | succ p ih =>
    intro i n q c hin hc
    subst hin
    have h1 := rowIterU F ms ws xs hms hws hxs i n (p + 1) q c (by
      have : i + n ≤ (p + 1 + 1) * (i + n) := Nat.le_mul_of_pos_left _ (by omega)
      omega)
    have sX := MEs_sym4 xs (fun e he => (hxs e he).1)
    have hcc : c + (i + n) ≤ F.N := by
      have : i + n ≤ (p + 1 + 1) * (i + n) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have sH' := F.sym (c + (i + n)) hcc
    have hS : Sym4 (MEs xs ++ 1 :: (F.Hc (c + (i + n)) ++ 0 :: F.Zt)) :=
      sX.app (Sym4.cons (by simp [ALL]) sH')
    have hP : Sym4 (MEnc ms ++ List.replicate (i + n) 2 ++ [3] ++ 1 :: (MEs ws ++ [1])) := by
      have sW := MEs_sym4 ws (fun e he => (hws e he).1)
      exact (((MEnc_sym4 ms).app (Sym4.rep _ _ (by simp [ALL]))).app (by simp [ALL])).app
        (Sym4.cons (by simp [ALL]) (sW.app (by simp [ALL])))
    have h2 := (gd2Row _ hS q (p + 1) _ hP).1 p rfl
    have h3 := ih (i + n) 0 (q + 1) (c + (i + n)) (by omega) (by
      have : (p + 1 + 1) * (i + n) = (p + 1) * (i + n) + (i + n) := by rw [Nat.succ_mul]
      omega)
    have e1 : (p + 1 + 1) * (i + n) = (i + n) + (p + 1) * (i + n) := by
      rw [Nat.succ_mul, Nat.add_comm]
    have e2 : p + 1 + q + 1 = p + (q + 1) + 1 := by omega
    rw [e1, e2, ← Nat.add_assoc]
    refine ((h1.trans h2).trans (h3.of_eq (by simp [List.append_assoc]) rfl)).of_eq rfl ?_
    have e3 : 1 + (p + (q + 1)) = 1 + (p + q + 1) := by omega
    have e4 : c + (i + n) + (p + 1) * (i + n) = c + (i + n + (p + 1) * (i + n)) := by omega
    have e5 : p + (q + 1) + 1 = p + q + 1 + 1 := by omega
    simp [List.append_assoc, e4, e5]



/-- `innerLoopU` started from the left end (head before the marked prefix). -/
theorem innerLoopU0 (F : HFam) (ms : List Nat) (ws xs : List (List Nat))
    (mb : List Nat) (hms : ∀ e ∈ ms, 1 ≤ e) (hws : ∀ e ∈ ws, Bits e ∧ e ≠ []) (hmb : Bits mb)
    (hxs : ∀ e ∈ xs, Bits e ∧ e ≠ []) (n c : Nat) (hc : c + n ≤ F.N) :
    zgiLogic.Reach
      (hdR QG.gIL1b [] (MEnc ms ++ List.replicate 0 2 ++ List.replicate (n + 1) 3 ++ 1 ::
        (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (F.Hc c ++ 0 :: F.Zt))))))
      (hdR QG.gD1 (MEnc ms ++ List.replicate (0 + n) 2 ++ [3])
        (1 :: (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (F.Hc (c + n) ++ 0 :: F.Zt)))))) := by
  have := ilSkipList (List.replicate 0 2 ++ List.replicate (n + 1) 3 ++ 1 :: (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (F.Hc c ++ 0 :: F.Zt)))))
    (by simp [ALL, MEs_sym4 ws (fun e he => (hws e he).1), hmb.sym4, MEs_sym4 xs (fun e he => (hxs e he).1), F.sym c (by omega)]) ms [] hms (by simp [ALL])
  have h2 := innerLoopU F QG.gIL1b (Or.inl rfl) ms ws xs mb hms hws hmb hxs n 0 c hc
  simp only [List.nil_append] at this
  exact (this.of_eq (by simp [List.append_assoc]) rfl).trans h2

/-- The column part over an `H`-family: from the start of the target to the deletion mark. -/
theorem colPartU (F : HFam) (ms : List Nat) (ws : List (List Nat)) (x0 : List Nat) (xs' : List (List Nat)) (r : List Nat)
    (hms : ∀ e ∈ ms, 1 ≤ e) (hws : ∀ e ∈ ws, Bits e ∧ e ≠ [])
    (hx0 : Bits x0 ∧ x0 ≠ []) (hxs : ∀ e ∈ xs', Bits e ∧ e ≠ [])
    (hr : Sym4 r) (m n c : Nat) (hc : c + n ≤ F.N) (T : List (List Nat)) (hTb : ∀ t ∈ T, Bits t)
    (hT : F.Hc (c + n) = MP T ++ 3 :: 3 :: r) :
    zgiLogic.Reach
      (hdR QG.gIL1b [] (MEnc ms ++ List.replicate 0 2 ++ List.replicate (n + 1) 3 ++ 1 ::
        (MEs ws ++ 1 :: (List.replicate m 3 ++ 1 :: (MEs (x0 :: xs') ++ 1 :: (F.Hc c ++ 0 :: F.Zt))))))
      (hd QG.gGL (MEnc ms ++ List.replicate n 2 ++ 3 :: 1 :: (MEs ws ++ 1 :: (List.replicate m 3 ++ 1 ::
          (MEs (x0 :: xs') ++ 1 :: (MU T ++ [3]))))) (2 :: (r ++ 0 :: F.Zt))) := by
  have hZ0 : Sym4 (0 :: F.Zt) := Sym4.cons (by simp [ALL]) F.hZ
  have hxs0 : ∀ e ∈ x0 :: xs', Bits e ∧ e ≠ [] := by
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact hx0
    · exact hxs e he
  have hRt : Sym4 (3 :: 3 :: (r ++ 0 :: F.Zt)) := by simp [ALL, hr, hZ0]
  have h1 := innerLoopU0 F ms ws (x0 :: xs') (List.replicate m 3) hms hws (bits_rep3 m) hxs0 n c hc
  rw [hT] at h1
  have e0 : MP T ++ 3 :: 3 :: r ++ 0 :: F.Zt = MP T ++ (3 :: 3 :: (r ++ 0 :: F.Zt)) := by simp
  rw [e0] at h1
  have sW := MEs_sym4 ws (fun e he => (hws e he).1)
  have sX := MEs_sym4 (x0 :: xs') (fun e he => (hxs0 e he).1)
  have sH : Sym4 (MP (T) ++ (3 :: 3 :: (r ++ 0 :: F.Zt))) := (MP_sym4 _ hTb).app hRt
  have sR3 : Sym4 (MEs (x0 :: xs') ++ 1 :: (MP (T) ++ (3 :: 3 :: (r ++ 0 :: F.Zt)))) :=
    sX.app (Sym4.cons (by simp [ALL]) sH)
  have sR4 : Sym4 (List.replicate m 3 ++ 1 :: (MEs (x0 :: xs') ++ 1 :: (MP (T) ++ (3 :: 3 :: (r ++ 0 :: F.Zt))))) :=
    (Sym4.rep _ _ (by simp [ALL])).app (Sym4.cons (by simp [ALL]) sR3)
  have sP0 : Sym4 (MEnc ms ++ List.replicate (0 + n) 2 ++ [3]) :=
    ((MEnc_sym4 ms).app (Sym4.rep _ _ (by simp [ALL]))).app (by simp [ALL])
  have h2 := wd1EndIn (MEnc ms ++ List.replicate (0 + n) 2 ++ [3]) (MEs ws ++ 1 :: (List.replicate m 3 ++ 1 ::
    (MEs (x0 :: xs') ++ 1 :: (MP (T) ++ (3 :: 3 :: (r ++ 0 :: F.Zt))))))
    sP0 (sW.app (Sym4.cons (by simp [ALL]) sR4))
  have h3 := wd1Walk _ sR4 ws (MEnc ms ++ List.replicate (0 + n) 2 ++ [3] ++ [1]) hws (sP0.app (by simp [ALL]))
  have sP1 : Sym4 (MEnc ms ++ List.replicate (0 + n) 2 ++ [3] ++ [1] ++ MEs ws ++ [1]) :=
    ((sP0.app (by simp [ALL])).app sW).app (by simp [ALL])
  have h4 := gd2Skips (1 :: (MEs (x0 :: xs') ++ 1 :: (MP (T) ++ (3 :: 3 :: (r ++ 0 :: F.Zt)))))
    (Sym4.cons (by simp [ALL]) sR3) m _ sP1
  have sP2 : Sym4 (MEnc ms ++ List.replicate (0 + n) 2 ++ [3] ++ [1] ++ MEs ws ++ [1] ++ List.replicate m 3) :=
    sP1.app (Sym4.rep _ _ (by simp [ALL]))
  have h5 := gd2Col _ (MEs (x0 :: xs') ++ 1 :: (MP (T) ++ (3 :: 3 :: (r ++ 0 :: F.Zt)))) sP2 sR3
  have sQ : Sym4 (MP (T) ++ (3 :: 3 :: (r ++ 0 :: F.Zt))) := sH
  have sXs : Sym4 (MEs xs' ++ 1 :: (MP (T) ++ (3 :: 3 :: (r ++ 0 :: F.Zt)))) :=
    (MEs_sym4 xs' (fun e he => (hxs e he).1)).app (Sym4.cons (by simp [ALL]) sQ)
  have sP3 : Sym4 (MEnc ms ++ List.replicate (0 + n) 2 ++ [3] ++ [1] ++ MEs ws ++ [1] ++ List.replicate m 3 ++ [1]) :=
    sP2.app (by simp [ALL])
  have h6 := n2Cells _ sXs x0 _ hx0.1 sP3
  have sP4 : Sym4 (MEnc ms ++ List.replicate (0 + n) 2 ++ [3] ++ [1] ++ MEs ws ++ [1] ++ List.replicate m 3 ++ [1] ++ x0 ++ [1]) :=
    (sP3.app hx0.1.sym4).app (by simp [ALL])
  have h7 := n2Walk _ sQ xs' _ hxs sP4
  have sP5 : Sym4 (MEnc ms ++ List.replicate (0 + n) 2 ++ [3] ++ [1] ++ MEs ws ++ [1] ++ List.replicate m 3 ++ [1] ++ x0 ++ [1] ++ MEs xs' ++ [1]) :=
    (sP4.app (MEs_sym4 xs' (fun e he => (hxs e he).1))).app (by simp [ALL])
  have h8 := huWalk (3 :: 3 :: (r ++ 0 :: F.Zt)) hRt (T) _ hTb sP5
  have sP6 : Sym4 (MEnc ms ++ List.replicate (0 + n) 2 ++ [3] ++ [1] ++ MEs ws ++ [1] ++ List.replicate m 3 ++ [1] ++ x0 ++ [1] ++ MEs xs' ++ [1] ++ MU (T)) :=
    sP5.app (MU_sym4 _ hTb)
  have h9 := huFound (MEnc ms ++ List.replicate (0 + n) 2 ++ [3] ++ [1] ++ MEs ws ++ [1] ++ List.replicate m 3 ++ [1] ++ x0 ++ [1] ++ MEs xs' ++ [1] ++ MU (T)) (3 :: (r ++ 0 :: F.Zt)) sP6 (by simp [ALL, hr, hZ0])
  have h10 := hcMark (MEnc ms ++ List.replicate (0 + n) 2 ++ [3] ++ [1] ++ MEs ws ++ [1] ++ List.replicate m 3 ++ [1] ++ x0 ++ [1] ++ MEs xs' ++ [1] ++ MU (T) ++ [3]) (r ++ 0 :: F.Zt) (sP6.app (by simp [ALL])) (hr.app hZ0)
  simp only [MEs, ME, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append,
    Nat.zero_add, List.replicate_zero, MU_append, MU] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ⊢
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8.trans (h9.trans h10))))))))



/-- The column part up to the unmarking walk: all but the head's passes, ending in `gHU`. -/
theorem colPre (F : HFam) (ms : List Nat) (ws : List (List Nat)) (x0 : List Nat) (xs' : List (List Nat))
    (hms : ∀ e ∈ ms, 1 ≤ e) (hws : ∀ e ∈ ws, Bits e ∧ e ≠ [])
    (hx0 : Bits x0 ∧ x0 ≠ []) (hxs : ∀ e ∈ xs', Bits e ∧ e ≠ [])
    (m n c : Nat) (hc : c + n ≤ F.N) (T : List (List Nat)) (R : List Nat) (hTb : ∀ t ∈ T, Bits t) (hR : Sym4 R)
    (hT : F.Hc (c + n) ++ 0 :: F.Zt = MP T ++ R) :
    zgiLogic.Reach
      (hdR QG.gIL1b [] (MEnc ms ++ List.replicate 0 2 ++ List.replicate (n + 1) 3 ++ 1 ::
        (MEs ws ++ 1 :: (List.replicate m 3 ++ 1 :: (MEs (x0 :: xs') ++ 1 :: (F.Hc c ++ 0 :: F.Zt))))))
      (hdR QG.gHU (MEnc ms ++ List.replicate n 2 ++ [3] ++ [1] ++ MEs ws ++ [1] ++ List.replicate m 3 ++ [1] ++ x0 ++ [1] ++
        MEs xs' ++ [1]) (MP T ++ R)) := by
  have hxs0 : ∀ e ∈ x0 :: xs', Bits e ∧ e ≠ [] := by
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact hx0
    · exact hxs e he
  have h1 := innerLoopU0 F ms ws (x0 :: xs') (List.replicate m 3) hms hws (bits_rep3 m) hxs0 n c hc
  rw [hT] at h1
  have sW := MEs_sym4 ws (fun e he => (hws e he).1)
  have sX := MEs_sym4 (x0 :: xs') (fun e he => (hxs0 e he).1)
  have sH : Sym4 (MP T ++ R) := (MP_sym4 _ hTb).app hR
  have sR3 : Sym4 (MEs (x0 :: xs') ++ 1 :: (MP T ++ R)) :=
    sX.app (Sym4.cons (by simp [ALL]) sH)
  have sR4 : Sym4 (List.replicate m 3 ++ 1 :: (MEs (x0 :: xs') ++ 1 :: (MP T ++ R))) :=
    (Sym4.rep _ _ (by simp [ALL])).app (Sym4.cons (by simp [ALL]) sR3)
  have sP0 : Sym4 (MEnc ms ++ List.replicate (0 + n) 2 ++ [3]) :=
    ((MEnc_sym4 ms).app (Sym4.rep _ _ (by simp [ALL]))).app (by simp [ALL])
  have h2 := wd1EndIn (MEnc ms ++ List.replicate (0 + n) 2 ++ [3]) (MEs ws ++ 1 :: (List.replicate m 3 ++ 1 ::
    (MEs (x0 :: xs') ++ 1 :: (MP T ++ R))))
    sP0 (sW.app (Sym4.cons (by simp [ALL]) sR4))
  have h3 := wd1Walk _ sR4 ws (MEnc ms ++ List.replicate (0 + n) 2 ++ [3] ++ [1]) hws (sP0.app (by simp [ALL]))
  have sP1 : Sym4 (MEnc ms ++ List.replicate (0 + n) 2 ++ [3] ++ [1] ++ MEs ws ++ [1]) :=
    ((sP0.app (by simp [ALL])).app sW).app (by simp [ALL])
  have h4 := gd2Skips (1 :: (MEs (x0 :: xs') ++ 1 :: (MP T ++ R)))
    (Sym4.cons (by simp [ALL]) sR3) m _ sP1
  have sP2 : Sym4 (MEnc ms ++ List.replicate (0 + n) 2 ++ [3] ++ [1] ++ MEs ws ++ [1] ++ List.replicate m 3) :=
    sP1.app (Sym4.rep _ _ (by simp [ALL]))
  have h5 := gd2Col _ (MEs (x0 :: xs') ++ 1 :: (MP T ++ R)) sP2 sR3
  have sQ : Sym4 (MP T ++ R) := sH
  have sXs : Sym4 (MEs xs' ++ 1 :: (MP T ++ R)) :=
    (MEs_sym4 xs' (fun e he => (hxs e he).1)).app (Sym4.cons (by simp [ALL]) sQ)
  have sP3 : Sym4 (MEnc ms ++ List.replicate (0 + n) 2 ++ [3] ++ [1] ++ MEs ws ++ [1] ++ List.replicate m 3 ++ [1]) :=
    sP2.app (by simp [ALL])
  have h6 := n2Cells _ sXs x0 _ hx0.1 sP3
  have sP4 : Sym4 (MEnc ms ++ List.replicate (0 + n) 2 ++ [3] ++ [1] ++ MEs ws ++ [1] ++ List.replicate m 3 ++ [1] ++ x0 ++ [1]) :=
    (sP3.app hx0.1.sym4).app (by simp [ALL])
  have h7 := n2Walk _ sQ xs' _ hxs sP4
  have sP5 : Sym4 (MEnc ms ++ List.replicate (0 + n) 2 ++ [3] ++ [1] ++ MEs ws ++ [1] ++ List.replicate m 3 ++ [1] ++ x0 ++ [1] ++ MEs xs' ++ [1]) :=
    (sP4.app (MEs_sym4 xs' (fun e he => (hxs e he).1))).app (by simp [ALL])
  simp only [MEs, ME, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append,
    Nat.zero_add, List.replicate_zero] at h1 h2 h3 h4 h5 h6 h7 ⊢
  exact (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))).of_eq (by simp [List.append_assoc]) (by simp [List.append_assoc])

/-- The row part fails: `H` runs out. -/
theorem rowLoopF (F : HFam) (ms : List Nat) (ws xs : List (List Nat))
    (hms : ∀ e ∈ ms, 1 ≤ e) (hws : ∀ e ∈ ws, Bits e ∧ e ≠ []) (hxs : ∀ e ∈ xs, Bits e ∧ e ≠ [])
    (nn : Nat) : ∀ (p i n q c : Nat), i + n = nn → c ≤ F.N → F.N < c + (p + 1) * nn →
    FailsTo
      (hd QG.gTR1 (MEnc ms ++ List.replicate i 2 ++ 3 :: (List.replicate n 3 ++ 1 :: (MEs ws ++ 1 :: List.replicate p 3)))
        (2 :: (List.replicate q 2 ++ 1 :: (MEs xs ++ 1 :: (F.Hc c ++ 0 :: F.Zt)))))
      (UG ms ws xs nn (p + q + 1) F.Hu) F.Zt := by
  intro p
  induction p with
  | zero =>
    intro i n q c hin hc hf
    subst hin
    exact rowIterF F ms ws xs hms hws hxs i n 0 q c hc (by simpa using hf)
  | succ p ih =>
    intro i n q c hin hc hf
    subst hin
    by_cases hs : c + (i + n) ≤ F.N
    · have h1 := rowIterU F ms ws xs hms hws hxs i n (p + 1) q c hs
      have sX := MEs_sym4 xs (fun e he => (hxs e he).1)
      have sH' := F.sym (c + (i + n)) hs
      have hS : Sym4 (MEs xs ++ 1 :: (F.Hc (c + (i + n)) ++ 0 :: F.Zt)) :=
        sX.app (Sym4.cons (by simp [ALL]) sH')
      have hP : Sym4 (MEnc ms ++ List.replicate (i + n) 2 ++ [3] ++ 1 :: (MEs ws ++ [1])) := by
        have sW := MEs_sym4 ws (fun e he => (hws e he).1)
        exact (((MEnc_sym4 ms).app (Sym4.rep _ _ (by simp [ALL]))).app (by simp [ALL])).app
          (Sym4.cons (by simp [ALL]) (sW.app (by simp [ALL])))
      have h2 := (gd2Row _ hS q (p + 1) _ hP).1 p rfl
      have h3 := ih (i + n) 0 (q + 1) (c + (i + n)) (by omega) hs (by
        have : (p + 1 + 1) * (i + n) = (p + 1) * (i + n) + (i + n) := by rw [Nat.succ_mul]
        omega)
      refine FailsTo.pre (h1.trans h2) (FailsTo.ofCfg ?_ (FailsTo.cast ?_ h3))
      · simp [List.append_assoc]
      · have e5 : p + (q + 1) + 1 = p + 1 + q + 1 := by omega
        simp [e5]
    · exact FailsTo.cast (by simp [UG]) (rowIterF F ms ws xs hms hws hxs i n (p + 1) q c hc (by omega))


theorem MU_noB : ∀ ts : List (List Nat), (∀ t ∈ ts, Bits t) → NoB (MU ts)
  | [], _ => NoB.nil
  | t :: ts, h => by
    have := MU_noB ts (fun u hu => h u (List.mem_cons_of_mem _ hu))
    have ht := (h t (List.mem_cons_self ..)).noB
    simp only [MU, NoB_cons_iff, NoB_app_iff]
    simp [NB, ht, this]

theorem hu2EndB (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gHU2 P (0 :: R)) (hd QG.gFG P (0 :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 0, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 0, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem hu2Walk0 (R : List Nat) (hR : Sym4 R) : ∀ (t P : List Nat), Bits t → Sym4 P →
    zgiLogic.Reach (hdR QG.gHU2 P (t ++ R)) (hdR QG.gHU2 (P ++ t) R)
  | [], P, _, _ => by simpa using (LTM.Reach.refl _ _)
  | b :: t, P, ht, hP => by
    have hb := ht b (List.mem_cons_self ..)
    have ht' : Bits t := fun a ha => ht a (List.mem_cons_of_mem _ ha)
    have hR1 : Sym4 (t ++ R) := by simp [ALL, hR, ht'.sym4]
    have hP' : Sym4 (P ++ [b]) := by
      rcases mem_bits hb with rfl | rfl <;> simp [ALL, hP]
    have h2 := hu2Walk0 R hR t (P ++ [b]) ht' hP'
    rcases mem_bits hb with rfl | rfl
    · exact ((hu2Cell2 P (t ++ R) hP hR1).of_eq rfl rfl).trans (h2.of_eq rfl (by simp))
    · exact ((hu2Cell3 P (t ++ R) hP hR1).of_eq rfl rfl).trans (h2.of_eq rfl (by simp))

theorem unm_MP_MU : ∀ ts : List (List Nat), unm (MP ts) = unm (MU ts)
  | [] => rfl
  | t :: ts => by
    simp only [MP, MU, unm_cons, unm_append, unm_MP_MU ts, unm1]
    simp

/-- Failure at the end of the column part: nothing to delete. -/
theorem huFail (P : List Nat) (T : List (List Nat)) (R0 Zt : List Nat) (hP : Sym4 P) (hPn : NoB P) (hPne : P ≠ [])
    (hTb : ∀ t ∈ T, Bits t) (hZ : Sym4 Zt)
    (hR : R0 = [] ∨ (∃ R1, NoB R1 ∧ R0 = 1 :: R1) ∨ (∃ tl, Bits tl ∧ R0 = 2 :: tl) ∨
      (∃ R1, NoB R1 ∧ R0 = 3 :: 1 :: R1) ∨ R0 = [3] ∨ (∃ Q, NoB Q ∧ R0 = 3 :: 2 :: Q)) :
    FailsTo (hdR QG.gHU P (MP T ++ (R0 ++ 0 :: Zt))) (unm (P ++ (MP T ++ R0))) Zt := by
  have sZ0 : Sym4 (0 :: Zt) := Sym4.cons (by simp [ALL]) hZ
  have sU := MU_sym4 T hTb
  have nU := MU_noB T hTb
  have nP' : NoB (P ++ MU T) := hPn.app nU
  have sP' : Sym4 (P ++ MU T) := nP'.sym4
  have nb1 : NoB [1] := by simp [NB]
  have nb3 : NoB [3] := by simp [NB]
  have nb2 : NoB [2] := by simp [NB]
  have hPne' : P ++ MU T ≠ [] := by simp [hPne]
  have mk : ∀ {c : ZC} {A R1 : List Nat}, NoB A → NoB R1 → unm (A ++ R1) = unm (P ++ (MP T ++ R0)) →
      zgiLogic.Reach c (hdR QG.gFG A (R1 ++ 0 :: Zt)) → FailsTo c (unm (P ++ (MP T ++ R0))) Zt :=
    fun hA hR1 hu h => ⟨_, _, hA, hR1, hu, h⟩
  rcases hR with h0 | ⟨R1, hR1, h0⟩ | ⟨tl, htl, h0⟩ | ⟨R1, hR1, h0⟩ | h0 | ⟨Q, hQ, h0⟩ <;> subst h0
  · have hW := huWalk (0 :: Zt) sZ0 T P hTb hP
    have hE := huEndB (P ++ MU T) Zt sP' hZ
    refine mk nP' NoB.nil ?_ (((hW.of_eq rfl (by simp)).trans hE).trans (gfgR' _ _ nP' hPne' sZ0))
    simp [unm_append, unm_MP_MU]
  · have hW := huWalk (1 :: (R1 ++ 0 :: Zt)) (Sym4.cons (by simp [ALL]) (hR1.sym4.app sZ0)) T P hTb hP
    have hE := huEndM (P ++ MU T) (R1 ++ 0 :: Zt) sP' (hR1.sym4.app sZ0)
    refine mk (nP'.app nb1) hR1 ?_ ((hW.of_eq rfl (by simp)).trans hE)
    simp [unm_append, unm_MP_MU, unm1]
  · have sR : Sym4 (2 :: (tl ++ 0 :: Zt)) := Sym4.cons (by simp [ALL]) (htl.sym4.app sZ0)
    have hW := huWalk (2 :: (tl ++ 0 :: Zt)) sR T P hTb hP
    have hU := huUnm (P ++ MU T) (tl ++ 0 :: Zt) sP' (htl.sym4.app sZ0)
    have sP3 : Sym4 (P ++ MU T ++ [3]) := (nP'.app nb3).sym4
    have h2 := hu2Walk0 (0 :: Zt) sZ0 tl (P ++ MU T ++ [3]) htl sP3
    have sP4 : Sym4 (P ++ MU T ++ [3] ++ tl) := (nP'.app nb3 |>.app htl.noB).sym4
    have h3 := hu2EndB (P ++ MU T ++ [3] ++ tl) Zt sP4 hZ
    have nA := nP'.app nb3 |>.app htl.noB
    refine mk nA NoB.nil ?_ ((((hW.of_eq rfl (by simp)).trans hU).trans h2).trans h3 |>.trans (gfgR' _ _ nA (by simp) sZ0))
    simp [unm_append, unm_MP_MU, unm1]
  · have sR1 : Sym4 (R1 ++ 0 :: Zt) := hR1.sym4.app sZ0
    have hW := huWalk (3 :: 1 :: (R1 ++ 0 :: Zt)) (Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) sR1)) T P hTb hP
    have hF := huFound (P ++ MU T) (1 :: (R1 ++ 0 :: Zt)) sP' (Sym4.cons (by simp [ALL]) sR1)
    have nA := nP'.app nb3
    have hC := hcFail1 (P ++ MU T ++ [3]) (R1 ++ 0 :: Zt) nA.sym4 sR1
    refine mk (nA.app nb1) hR1 ?_ (((hW.of_eq rfl (by simp)).trans hF).trans hC)
    simp [unm_append, unm_MP_MU, unm1]
  · have hW := huWalk (3 :: 0 :: Zt) (Sym4.cons (by simp [ALL]) sZ0) T P hTb hP
    have hF := huFound (P ++ MU T) (0 :: Zt) sP' sZ0
    have nA := nP'.app nb3
    have hC := hcFail0 (P ++ MU T ++ [3]) Zt nA.sym4 hZ
    refine mk nA NoB.nil ?_ ((((hW.of_eq rfl (by simp)).trans hF).trans hC).trans (gfgR' _ _ nA (by simp) sZ0))
    simp [unm_append, unm_MP_MU, unm1]
  · have sR1 : Sym4 (Q ++ 0 :: Zt) := hQ.sym4.app sZ0
    have hW := huWalk (3 :: 2 :: (Q ++ 0 :: Zt)) (Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) sR1)) T P hTb hP
    have hF := huFound (P ++ MU T) (2 :: (Q ++ 0 :: Zt)) sP' (Sym4.cons (by simp [ALL]) sR1)
    have nA := nP'.app nb3
    have hC := hcFail2 (P ++ MU T ++ [3]) (Q ++ 0 :: Zt) nA.sym4 sR1
    refine mk (nA.app nb2) hQ ?_ (((hW.of_eq rfl (by simp)).trans hF).trans hC)
    simp [unm_append, unm_MP_MU, unm1]



/-- The column part fails because `H` runs out during the passes. -/
theorem colPartF1 (F : HFam) (ms : List Nat) (ws : List (List Nat)) (x0 : List Nat) (xs' : List (List Nat))
    (hms : ∀ e ∈ ms, 1 ≤ e) (hws : ∀ e ∈ ws, Bits e ∧ e ≠ [])
    (hx0 : Bits x0 ∧ x0 ≠ []) (hxs : ∀ e ∈ xs', Bits e ∧ e ≠ [])
    (m n c : Nat) (hc : c ≤ F.N) (hn : F.N < c + n) :
    FailsTo
      (hdR QG.gIL1b [] (MEnc ms ++ List.replicate 0 2 ++ List.replicate (n + 1) 3 ++ 1 ::
        (MEs ws ++ 1 :: (List.replicate m 3 ++ 1 :: (MEs (x0 :: xs') ++ 1 :: (F.Hc c ++ 0 :: F.Zt))))))
      (UG ms ws (x0 :: xs') n m F.Hu) F.Zt := by
  have hxs0 : ∀ e ∈ x0 :: xs', Bits e ∧ e ≠ [] := by
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact hx0
    · exact hxs e he
  have := ilSkipList (List.replicate 0 2 ++ List.replicate (n + 1) 3 ++ 1 :: (MEs ws ++ 1 :: (List.replicate m 3 ++ 1 :: (MEs (x0 :: xs') ++ 1 :: (F.Hc c ++ 0 :: F.Zt)))))
    (by simp [ALL, MEs_sym4 ws (fun e he => (hws e he).1), (bits_rep3 m).sym4, MEs_sym4 (x0 :: xs') (fun e he => (hxs0 e he).1), F.sym c hc]) ms [] hms (by simp [ALL])
  have h2 := innerLoopF F QG.gIL1b (Or.inl rfl) ms ws (x0 :: xs') (List.replicate m 3) hms hws (bits_rep3 m) hxs0 n 0 c hc hn
  simp only [List.nil_append] at this
  refine FailsTo.pre (this.of_eq (by simp [List.append_assoc]) rfl) (FailsTo.cast ?_ h2)
  simp [UG, unm_append, unm_rep3, unm_MEnc, F.hu_unm, unm1]

/-- The column part fails after the passes: no target, a short target, or a used target. -/
theorem colPartF2 (F : HFam) (ms : List Nat) (ws : List (List Nat)) (x0 : List Nat) (xs' : List (List Nat))
    (hms : ∀ e ∈ ms, 1 ≤ e) (hws : ∀ e ∈ ws, Bits e ∧ e ≠ [])
    (hx0 : Bits x0 ∧ x0 ≠ []) (hxs : ∀ e ∈ xs', Bits e ∧ e ≠ [])
    (m n c : Nat) (hc : c + n ≤ F.N) (T : List (List Nat)) (R0 : List Nat) (hTb : ∀ t ∈ T, Bits t)
    (hT : F.Hc (c + n) ++ 0 :: F.Zt = MP T ++ (R0 ++ 0 :: F.Zt))
    (hR : R0 = [] ∨ (∃ R1, NoB R1 ∧ R0 = 1 :: R1) ∨ (∃ tl, Bits tl ∧ R0 = 2 :: tl) ∨
      (∃ R1, NoB R1 ∧ R0 = 3 :: 1 :: R1) ∨ R0 = [3] ∨ (∃ Q, NoB Q ∧ R0 = 3 :: 2 :: Q)) :
    FailsTo
      (hdR QG.gIL1b [] (MEnc ms ++ List.replicate 0 2 ++ List.replicate (n + 1) 3 ++ 1 ::
        (MEs ws ++ 1 :: (List.replicate m 3 ++ 1 :: (MEs (x0 :: xs') ++ 1 :: (F.Hc c ++ 0 :: F.Zt))))))
      (UG ms ws (x0 :: xs') n m F.Hu) F.Zt := by
  have hxs0 : ∀ e ∈ x0 :: xs', Bits e ∧ e ≠ [] := by
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact hx0
    · exact hxs e he
  have hR0 : Sym4 (R0 ++ 0 :: F.Zt) := by
    have := F.sym (c + n) hc
    rw [hT] at this
    exact fun a ha => this a (List.mem_append_right _ ha)
  have h1 := colPre F ms ws x0 xs' hms hws hx0 hxs m n c hc T (R0 ++ 0 :: F.Zt) hTb hR0 hT
  have nW := MEs_noB ws (fun e he => (hws e he).1)
  have nX := MEs_noB xs' (fun e he => (hxs e he).1)
  have nPP : NoB (MEnc ms ++ List.replicate n 2 ++ [3] ++ [1] ++ MEs ws ++ [1] ++ List.replicate m 3 ++ [1] ++ x0 ++ [1] ++
        MEs xs' ++ [1]) := by
    simp [NB, MEnc_nb, nW, nX, hx0.1.noB]
  have h2 := huFail _ T R0 F.Zt nPP.sym4 nPP (by simp) hTb F.hZ hR
  refine FailsTo.pre h1 (FailsTo.cast ?_ h2)
  have hH : MP T ++ R0 = F.Hc (c + n) := by
    have := hT
    rw [← List.append_assoc] at this
    exact (List.append_cancel_right this).symm
  rw [hH]
  have hun := F.un (c + n) hc
  simp [UG, unm_append, unm_rep3, unm_MEnc, unm_rep2, hun, unm1, List.append_assoc, MEs, ME, List.replicate_succ']


/-! ### The row part starts: `gM1` walks left to the last unmarked cell of `m` and marks it -/

theorem gm1Pass (P R : List Nat) (a : Nat) (ha : a = 1 ∨ a = 2) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hd QG.gM1 (P ++ [a]) R) (hd QG.gM1 P (a :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  rcases ha with rfl | rfl
  · exact checkTT (env := [P, R]) (E := []) (k := 3) hV trivial
      (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkTT (env := [P, R]) (E := []) (k := 3) hV trivial
      (ls := [.blk 0 .id, .sym 2]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 2, .blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gm1Mark (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hd QG.gM1 (P ++ [3]) R) (hd QG.gTR1 P (2 :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [P, R]) (E := []) (k := 3) hV trivial (q' := QG.gTR1)
    (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 2, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gm1Walk (Q : List Nat) (hQ : Sym4 Q) : ∀ (n : Nat) (Z R : List Nat), Z.length = n →
    (∀ a ∈ Z, a = 1 ∨ a = 2) → Sym4 R →
    zgiLogic.Reach (hd QG.gM1 (Q ++ 3 :: Z) R) (hd QG.gTR1 Q (2 :: (Z ++ R))) := by
  intro n
  induction n with
  | zero =>
    intro Z R hl _ hR
    have : Z = [] := List.length_eq_zero_iff.1 hl
    subst this
    simpa using gm1Mark Q R hQ hR
  | succ n ih =>
    intro Z R hl hZ hR
    obtain ⟨Z0, a, hZa⟩ := (List.eq_nil_or_concat Z).resolve_left (by rintro rfl; simp at hl)
    rw [List.concat_eq_append] at hZa
    subst hZa
    have ha := hZ a (by simp)
    have hZ0 : ∀ b ∈ Z0, b = 1 ∨ b = 2 := fun b hb => hZ b (by simp [hb])
    have sZ0 : Sym4 (Q ++ 3 :: Z0) := by
      refine hQ.app (Sym4.cons (by simp [ALL]) ?_)
      intro b hb; rcases hZ0 b hb with rfl | rfl <;> simp [ALL]
    have sR : Sym4 (a :: R) := Sym4.cons (by rcases ha with rfl | rfl <;> simp [ALL]) hR
    have h1 := gm1Pass (Q ++ 3 :: Z0) R a ha sZ0 hR
    have h2 := ih Z0 (a :: R) (by simpa using hl) hZ0 sR
    exact (h1.of_eq (by simp) rfl).trans (h2.of_eq rfl (by simp))


theorem MEs_append (a b : List (List Nat)) : MEs (a ++ b) = MEs a ++ MEs b := by
  induction a with
  | nil => rfl
  | cons c a ih => simp [MEs, ih, List.append_assoc]

theorem MEnc_MEs : ∀ l : List Nat, MEnc l = MEs (l.map fun e => List.replicate e 2)
  | [] => rfl
  | e :: l => by simp [MEnc, MEs, ME, MEnc_MEs l]

/-- The row part of an edge, from the found label `x` to the end of the row loop. -/
theorem edgeRow (F : HFam) (ms Wr d X' : List Nat) (n x p c : Nat)
    (hms : ∀ e ∈ ms, 1 ≤ e) (hWr : ∀ e ∈ Wr, 1 ≤ e) (hdd : ∀ e ∈ d, 1 ≤ e) (hX' : ∀ e ∈ X', 1 ≤ e) (hx : 1 ≤ x)
    (hc : c ≤ F.N) (hcn : c + (p + 1) * n ≤ F.N) :
    zgiLogic.Reach
      (hd QG.gM1 (MEnc ms ++ Enc ((n + 1) :: Wr) ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]) ++ MEnc d ++ List.replicate x 2)
        (1 :: (Enc X' ++ 1 :: (F.Hc c ++ 0 :: F.Zt))))
      (hd QG.gGL (MEnc ms ++ List.replicate n 2 ++ 3 :: 1 :: MEs (Wr.map fun e => List.replicate e 3))
        (1 :: (List.replicate (p + 0 + 1) 2 ++ 1 ::
          (MEs ((d.map fun e => List.replicate e 2) ++ List.replicate x 2 :: X'.map fun e => List.replicate e 3) ++ 1 ::
            (F.Hc (c + (p + 1) * n) ++ 0 :: F.Zt))))) := by
  have hws := Enc_entries Wr hWr
  have hxs : ∀ e ∈ (d.map fun e => List.replicate e 2) ++ List.replicate x 2 :: X'.map fun e => List.replicate e 3,
      Bits e ∧ e ≠ [] := by
    intro e he
    simp only [List.mem_append, List.mem_cons, List.mem_map] at he
    rcases he with ⟨v, hv, rfl⟩ | rfl | ⟨v, hv, rfl⟩
    · exact ⟨bits_rep2 v, by have := hdd v hv; intro h; have := congrArg List.length h; simp at this; omega⟩
    · exact ⟨bits_rep2 x, by intro h; have := congrArg List.length h; simp at this; omega⟩
    · exact ⟨bits_rep3 v, by have := hX' v hv; intro h; have := congrArg List.length h; simp at this; omega⟩
  have sX' : Sym4 (Enc X' ++ 1 :: (F.Hc c ++ 0 :: F.Zt)) := by
    have := Enc_o13 X'
    refine Sym4.app (fun a ha => ?_) (Sym4.cons (by simp [ALL]) (F.sym c hc))
    have := Enc_o13 X' a ha; simp [O13, ALL] at this ⊢; omega
  have sQ : Sym4 (MEnc ms ++ Enc ((n + 1) :: Wr) ++ [1] ++ List.replicate p 3) := by
    refine (((MEnc_sym4 ms).app (fun a ha => ?_)).app (by simp [ALL])).app (Sym4.rep _ _ (by simp [ALL]))
    have := Enc_o13 ((n + 1) :: Wr) a ha; simp [O13, ALL] at this ⊢; omega
  have hZ : ∀ a ∈ [1] ++ MEnc d ++ List.replicate x 2, a = 1 ∨ a = 2 := by
    intro a ha
    simp only [List.mem_append, List.mem_singleton, List.mem_replicate] at ha
    rcases ha with (rfl | ha) | ⟨_, rfl⟩
    · left; rfl
    · have := MEnc_o12 d a ha; simp [O12] at this; omega
    · right; rfl
  have h1 := gm1Walk (MEnc ms ++ Enc ((n + 1) :: Wr) ++ [1] ++ List.replicate p 3) sQ _ ([1] ++ MEnc d ++ List.replicate x 2)
    (1 :: (Enc X' ++ 1 :: (F.Hc c ++ 0 :: F.Zt))) rfl hZ (Sym4.cons (by simp [ALL]) sX')
  have h2 := rowLoopU F ms (Wr.map fun e => List.replicate e 3)
    ((d.map fun e => List.replicate e 2) ++ List.replicate x 2 :: X'.map fun e => List.replicate e 3)
    hms hws hxs n p 0 n 0 c (by omega) hcn
  have h1' : zgiLogic.Reach
      (hd QG.gM1 (MEnc ms ++ Enc ((n + 1) :: Wr) ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]) ++ MEnc d ++ List.replicate x 2)
        (1 :: (Enc X' ++ 1 :: (F.Hc c ++ 0 :: F.Zt))))
      (hd QG.gTR1 (MEnc ms ++ List.replicate 0 2 ++ 3 :: (List.replicate n 3 ++ 1 :: (MEs (Wr.map fun e => List.replicate e 3) ++ 1 :: List.replicate p 3)))
        (2 :: (List.replicate 0 2 ++ 1 :: (MEs ((d.map fun e => List.replicate e 2) ++ List.replicate x 2 :: X'.map fun e => List.replicate e 3) ++ 1 :: (F.Hc c ++ 0 :: F.Zt))))) := by
    refine h1.of_eq (by simp [List.replicate_succ', List.append_assoc]) ?_
    simp [Enc_MEs, MEnc_MEs, MEs_append, MEs, ME, List.append_assoc, List.replicate_succ]
  exact h1'.trans h2


/-- After the row (or the column) part: back to the start of `X`, with `w` and `m` unmarked. -/
theorem toY1 (WL : List (List Nat)) (c R : List Nat) (hW : ∀ e ∈ WL, Bits e ∧ e ≠ [])
    (hc : Bits c) (hR : Sym4 R) :
    zgiLogic.Reach (hd QG.gGL (MEs WL) (1 :: (c ++ 1 :: R)))
      (hdR QG.gY1e (unm (MEs WL) ++ [1] ++ unm c ++ [1]) R) := by
  have nW := MEs_noB WL (fun e he => (hW e he).1)
  have sR : Sym4 (1 :: (c ++ 1 :: R)) := Sym4.cons (by simp [ALL]) (hc.sym4.app (Sym4.cons (by simp [ALL]) hR))
  have h1 := gglWalk (MEs WL) (1 :: (c ++ 1 :: R)) nW sR
  have h2 := phaseU WL c R [0] hW hc (by simp [ALL]) hR
  refine (h1.of_eq rfl (by simp)).trans (h2.of_eq rfl ?_)
  rw [show [0] ++ unm (MEs WL) ++ [1] ++ unm c ++ [1] = 0 :: (unm (MEs WL) ++ [1] ++ unm c ++ [1]) by simp, hdR_z0]


/-- The same, with the head at the end of the tape to the left of `X`'s remainder (after the column part). -/
theorem toY1g (WL : List (List Nat)) (c Rl Rr : List Nat) (hW : ∀ e ∈ WL, Bits e ∧ e ≠ [])
    (hc : Bits c) (hRl : NoB Rl) (hR : Sym4 Rr) :
    zgiLogic.Reach (hd QG.gGL (MEs WL ++ 1 :: (c ++ 1 :: Rl)) Rr)
      (hdR QG.gY1e (unm (MEs WL) ++ [1] ++ unm c ++ [1]) (Rl ++ Rr)) := by
  have nW := MEs_noB WL (fun e he => (hW e he).1)
  have nA : NoB (MEs WL ++ 1 :: (c ++ 1 :: Rl)) := by
    simp only [NoB_app_iff, NoB_cons_iff]
    simp [NB, nW, hc.noB, hRl]
  have h1 := gglWalk _ Rr nA hR
  have sR : Sym4 (Rl ++ Rr) := hRl.sym4.app hR
  have h2 := phaseU WL c (Rl ++ Rr) [0] hW hc (by simp [ALL]) sR
  refine (h1.of_eq rfl (by simp)).trans (h2.of_eq rfl ?_)
  rw [show [0] ++ unm (MEs WL) ++ [1] ++ unm c ++ [1] = 0 :: (unm (MEs WL) ++ [1] ++ unm c ++ [1]) by simp, hdR_z0]


/-! ### Label failure: the label has more cells but `w` is exhausted -/

theorem labelIterF (b : Bool) (ms : List Nat) (m : Nat) (d : List Nat) (j r' : Nat) (X0 Zt : List Nat)
    (hms : ∀ e ∈ ms, 1 ≤ e) (hX : NoB X0) (hZ : Sym4 Zt) :
    FailsTo
      (hdR (LP b) (MEnc ms ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d ++ List.replicate (j + 1) 2)
        (3 :: (List.replicate r' 3 ++ 1 :: (X0 ++ 0 :: Zt))))
      (unm (MEnc ms ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d ++ List.replicate (j + 1) 2 ++
        3 :: (List.replicate r' 3 ++ 1 :: X0))) Zt := by
  have hX' := hX.sym4
  have hRt : Sym4 (3 :: (List.replicate r' 3 ++ 1 :: (X0 ++ 0 :: Zt))) := by simp [ALL, hX', hZ]
  have hP0 : Sym4 (MEnc ms ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d ++ List.replicate (j + 1) 2) := by
    simp [ALL]
  have hP0n : NoB (MEnc ms ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d ++ List.replicate (j + 1) 2) := by
    simp [NB]
  have hA := lpMoreB b _ (List.replicate r' 3 ++ 1 :: (X0 ++ 0 :: Zt)) hP0 (by simp [ALL, hX', hZ])
  have hB := lw1Walk _ _ hP0n hRt
  have hR1 : Sym4 (1 :: (List.replicate m 3 ++ 1 :: (MEnc d ++ List.replicate (j + 1) 2 ++
      3 :: (List.replicate r' 3 ++ 1 :: (X0 ++ 0 :: Zt))))) := by
    simp [ALL, hX', hZ]
  have hC := lw2bSkipList (1 :: (List.replicate m 3 ++ 1 :: (MEnc d ++ List.replicate (j + 1) 2 ++
      3 :: (List.replicate r' 3 ++ 1 :: (X0 ++ 0 :: Zt))))) hR1 ms [0] hms (by simp [ALL])
  have hRest : Sym4 (List.replicate m 3 ++ 1 :: (MEnc d ++ List.replicate (j + 1) 2 ++
      3 :: (List.replicate r' 3 ++ 1 :: (X0 ++ 0 :: Zt)))) := by
    simp [ALL, hX', hZ]
  have hD := lw2bFail ([0] ++ MEnc ms) _ (by simp [ALL]) hRest
  have hAll := hA.trans (hB.trans ((hC.of_eq (by simp [MEnc, List.append_assoc]) rfl).trans (hD.of_eq rfl rfl)))
  refine FailsTo.mk' (A := MEnc ms ++ [1])
    (R1 := List.replicate m 3 ++ 1 :: (MEnc d ++ List.replicate (j + 1) 2 ++ 3 :: (List.replicate r' 3 ++ 1 :: X0)))
    (by simp [NB]) (by simp [NB, hX]) (by simp [List.append_assoc]) ?_
  refine hAll.of_eq (by simp [List.append_assoc]) ?_
  rw [show [0] ++ MEnc ms ++ [1] = 0 :: (MEnc ms ++ [1]) by simp]
  rw [hdR_z0]; simp [List.append_assoc]

theorem rep3_cons (j : Nat) (l : List Nat) : List.replicate j 3 ++ 3 :: l = 3 :: (List.replicate j 3 ++ l) := by
  induction j with
  | zero => simp
  | succ j ih => simp [List.replicate_succ, ih]

theorem labelFindF (m : Nat) (d : List Nat) (X0 Zt : List Nat) (hdd : ∀ e ∈ d, 1 ≤ e)
    (hX : NoB X0) (hZ : Sym4 Zt) :
    ∀ (r : Nat) (ms ws : List Nat) (j : Nat), (∀ e ∈ ms, 1 ≤ e) → (∀ e ∈ ws, 1 ≤ e) → ws.length < r →
    FailsTo
      (hdR QG.gY1e (MEnc ms ++ Enc ws ++ [1] ++ (List.replicate m 3 ++ [1]))
        (MEnc d ++ List.replicate j 2 ++ List.replicate (r + 1) 3 ++ 1 :: (X0 ++ 0 :: Zt)))
      (unm (MEnc ms ++ Enc ws ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d ++ List.replicate j 2 ++
        List.replicate (r + 1) 3 ++ 1 :: X0)) Zt := by
  have hX' := hX.sym4
  intro r
  induction r with
  | zero => intro ms ws j _ _ hr; simp at hr
  | succ r ih =>
    intro ms ws j hms hws hr
    have hL := lblWalk (List.replicate j 2 ++ List.replicate (r + 1 + 1) 3 ++ 1 :: (X0 ++ 0 :: Zt))
      (by simp [ALL, hX', hZ]) d false (MEnc ms ++ Enc ws ++ [1] ++ (List.replicate m 3 ++ [1])) hdd (by simp [ALL])
    simp only [Bool.false_xor] at hL
    have hM := lblMarkB (decide (d.length % 2 = 1)) (MEnc ms ++ Enc ws ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d)
      (List.replicate (r + 1) 3 ++ 1 :: (X0 ++ 0 :: Zt)) j (by simp [ALL]) (by simp [ALL, hX', hZ])
    cases ws with
    | nil =>
      have hI := labelIterF (decide (d.length % 2 = 1)) ms m d j r X0 Zt hms hX hZ
      refine FailsTo.pre ((hL.of_eq (by simp [List.append_assoc]) rfl).trans
        (hM.of_eq (by simp [List.replicate_succ, List.append_assoc]) rfl))
        (FailsTo.ofCfg ?_ (FailsTo.cast ?_ hI))
      · simp [Enc, List.replicate_succ, List.append_assoc]
      · simp [Enc, unm_append, unm_rep2, unm_rep3, unm1, List.replicate_succ, rep3_cons, List.append_assoc]
    | cons w1 ws' =>
      obtain ⟨v, rfl⟩ : ∃ v, w1 = v + 1 := ⟨w1 - 1, by have := hws w1 (List.mem_cons_self ..); omega⟩
      have hws' : ∀ e ∈ ws', 1 ≤ e := fun e he => hws e (List.mem_cons_of_mem _ he)
      have hI := labelIter (decide (d.length % 2 = 1)) ms ws' v m d j r (X0 ++ 0 :: Zt) hms hws' (by simp [ALL, hX', hZ])
      have hF := ih (ms ++ [v + 1]) ws' (j + 1) (by
          intro e he
          rcases List.mem_append.1 he with he | he
          · exact hms e he
          · simp at he; omega) hws' (by simp at hr; omega)
      refine FailsTo.pre ((hL.of_eq (by simp [List.append_assoc]) rfl).trans
        ((hM.of_eq (by simp [List.replicate_succ, List.append_assoc]) rfl).trans
          (hI.of_eq (by simp [List.replicate_succ, List.append_assoc]) rfl)))
        (FailsTo.ofCfg ?_ (FailsTo.cast ?_ hF))
      · simp [List.replicate_succ, List.append_assoc]
      · simp [unm_append, unm_rep2, unm_rep3, unm1, MEnc_append, Enc, MEnc, U, ME, List.replicate_succ, rep3_cons, List.append_assoc]

/-! ### The row half-step as a whole: from the start of `X` (label `x` unmarked) to the start of the next label -/

theorem rowHalf (F : HFam) (W Wr d X' : List Nat) (r n p c : Nat)
    (hW : ∀ e ∈ W, 1 ≤ e) (hdd : ∀ e ∈ d, 1 ≤ e) (hX' : ∀ e ∈ X', 1 ≤ e) (hdl : d.length % 2 = 0)
    (hr : W.drop r = (n + 1) :: Wr) (hc : c ≤ F.N) (hcn : c + (p + 1) * n ≤ F.N) :
    zgiLogic.Reach
      (hdR QG.gY1e (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]))
        (MEnc d ++ List.replicate (r + 1) 3 ++ 1 :: (Enc X' ++ 1 :: (F.Hc c ++ 0 :: F.Zt))))
      (hdR QG.gY1e (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]))
        (MEnc (d ++ [r + 1]) ++ Enc X' ++ 1 :: (F.Hc (c + (p + 1) * n) ++ 0 :: F.Zt))) := by
  have hrl : r ≤ W.length := by
    have := congrArg List.length hr
    simp at this; omega
  have hWr : ∀ e ∈ Wr, 1 ≤ e := by
    intro e he
    have : e ∈ W.drop r := by rw [hr]; exact List.mem_cons_of_mem _ he
    exact hW e (List.mem_of_mem_drop this)
  have hms : ∀ e ∈ W.take r, 1 ≤ e := fun e he => hW e (List.mem_of_mem_take he)
  have hZ0 : Sym4 (0 :: F.Zt) := Sym4.cons (by simp [ALL]) F.hZ
  have hXs : Sym4 (Enc X' ++ 1 :: (F.Hc c ++ 0 :: F.Zt)) := by
    refine Sym4.app (fun a ha => ?_) (Sym4.cons (by simp [ALL]) (F.sym c hc))
    have := Enc_o13 X' a ha; simp [O13, ALL] at this ⊢; omega
  have hL := labelFind (p + 1) d (Enc X' ++ 1 :: (F.Hc c ++ 0 :: F.Zt)) hdd hXs r [] W 0
    (by simp) hW hrl
  have hdf : decide (d.length % 2 = 1) = false := by simp [hdl]
  rw [hdf] at hL
  have hE := edgeRow F (W.take r) Wr d X' n (r + 1) p c hms hWr hdd hX' (by omega) hc hcn
  have hWL : ∀ e ∈ (W.take r).map (fun e => List.replicate e 2) ++ (List.replicate n 2 ++ [3]) :: Wr.map (fun e => List.replicate e 3),
      Bits e ∧ e ≠ [] := by
    intro e he
    simp only [List.mem_append, List.mem_cons, List.mem_map] at he
    rcases he with ⟨v, hv, rfl⟩ | rfl | ⟨v, hv, rfl⟩
    · exact ⟨bits_rep2 v, by have := hms v hv; intro h; have := congrArg List.length h; simp at this; omega⟩
    · refine ⟨fun a ha => ?_, by simp⟩
      rcases List.mem_append.1 ha with ha | ha
      · rw [List.eq_of_mem_replicate ha]; simp [bits]
      · simp at ha; subst ha; simp [bits]
    · exact ⟨bits_rep3 v, by have := hWr v hv; intro h; have := congrArg List.length h; simp at this; omega⟩
  have hRr : Sym4 (MEs ((d.map fun e => List.replicate e 2) ++ List.replicate (r + 1) 2 :: X'.map fun e => List.replicate e 3) ++ 1 ::
      (F.Hc (c + (p + 1) * n) ++ 0 :: F.Zt)) := by
    refine Sym4.app (MEs_sym4 _ ?_) (Sym4.cons (by simp [ALL]) (F.sym _ hcn))
    intro e he
    simp only [List.mem_append, List.mem_cons, List.mem_map] at he
    rcases he with ⟨v, hv, rfl⟩ | rfl | ⟨v, hv, rfl⟩
    · exact bits_rep2 v
    · exact bits_rep2 _
    · exact bits_rep3 v
  have hT := toY1 _ (List.replicate (p + 1) 2) _ hWL (bits_rep2 _) hRr
  have hLd : (LDone false) = QG.gM1 := rfl
  rw [hLd, hr] at hL
  refine (hL.of_eq (by simp [MEnc]) rfl).trans ((hE.of_eq (by simp [Enc, MEnc, List.append_assoc]) rfl).trans (hT.of_eq ?_ ?_))
  · simp [MEnc_MEs, MEs_append, MEs, ME, List.append_assoc, List.replicate_succ]
  · have e1 : MEs ((W.take r).map (fun e => List.replicate e 2) ++ (List.replicate n 2 ++ [3]) :: Wr.map (fun e => List.replicate e 3)) =
        MEnc (W.take r) ++ List.replicate n 2 ++ 3 :: 1 :: MEs (Wr.map fun e => List.replicate e 3) := by
      simp [MEnc_MEs, MEs_append, MEs, ME, List.append_assoc]
    have e2 : MEs ((d.map fun e => List.replicate e 2) ++ List.replicate (r + 1) 2 :: X'.map fun e => List.replicate e 3) =
        MEnc d ++ List.replicate (r + 1) 2 ++ 1 :: Enc X' := by
      simp [MEnc_MEs, Enc_MEs, MEs_append, MEs, ME, List.append_assoc]
    rw [e1, e2, show Enc W = Enc (W.take r) ++ Enc ((n + 1) :: Wr) from by rw [← Enc_append, ← hr, List.take_append_drop]]
    have u3 : unm (MEs (Wr.map fun e => List.replicate e 3)) = MEs (Wr.map fun e => List.replicate e 3) := by
      rw [← Enc_MEs, unm_Enc]
    simp [unm_append, unm_rep2, unm_rep3, unm1, unm_MEnc, u3, Enc_MEs, rep3_cons, MEs, ME, MEnc, MEnc_append, Enc, U,
      List.replicate_succ, List.append_assoc]
    done

/-- The column half-step as a whole. -/
theorem colHalf (F : HFam) (W Wr d X' : List Nat) (r n p c : Nat) (T : List (List Nat)) (r0 : List Nat)
    (hW : ∀ e ∈ W, 1 ≤ e) (hdd : ∀ e ∈ d, 1 ≤ e) (hX' : ∀ e ∈ X', 1 ≤ e) (hdl : d.length % 2 = 1)
    (hr : W.drop r = (n + 1) :: Wr) (hc : c + n ≤ F.N) (hTb : ∀ t ∈ T, Bits t)
    (hT : F.Hc (c + n) = MP T ++ 3 :: 3 :: r0) (hr0 : Sym4 r0) :
    zgiLogic.Reach
      (hdR QG.gY1e (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]))
        (MEnc d ++ List.replicate (r + 1) 3 ++ 1 :: (Enc X' ++ 1 :: (F.Hc c ++ 0 :: F.Zt))))
      (hdR QG.gY1e (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]))
        (MEnc (d ++ [r + 1]) ++ Enc X' ++ 1 :: (MU T ++ 3 :: 2 :: (r0 ++ 0 :: F.Zt)))) := by
  have hrl : r ≤ W.length := by
    have := congrArg List.length hr
    simp at this; omega
  have hWr : ∀ e ∈ Wr, 1 ≤ e := by
    intro e he
    have : e ∈ W.drop r := by rw [hr]; exact List.mem_cons_of_mem _ he
    exact hW e (List.mem_of_mem_drop this)
  have hms : ∀ e ∈ W.take r, 1 ≤ e := fun e he => hW e (List.mem_of_mem_take he)
  have hcc : c ≤ F.N := by omega
  have hXs : Sym4 (Enc X' ++ 1 :: (F.Hc c ++ 0 :: F.Zt)) := by
    refine Sym4.app (fun a ha => ?_) (Sym4.cons (by simp [ALL]) (F.sym c hcc))
    have := Enc_o13 X' a ha; simp [O13, ALL] at this ⊢; omega
  have hL := labelFind (p + 1) d (Enc X' ++ 1 :: (F.Hc c ++ 0 :: F.Zt)) hdd hXs r [] W 0
    (by simp) hW hrl
  have hdf : decide (d.length % 2 = 1) = true := by simp [hdl]
  rw [hdf] at hL
  obtain ⟨e, d', hdeq⟩ : ∃ e d', d = e :: d' := by
    cases d with
    | nil => simp at hdl
    | cons e d' => exact ⟨e, d', rfl⟩
  have hde : 1 ≤ e := hdd e (by simp [hdeq])
  have hd' : ∀ x ∈ d', 1 ≤ x := fun x hx => hdd x (by simp [hdeq, hx])
  have hLd : (LDone true) = QG.gIL0 := rfl
  rw [hLd, hr] at hL
  have hZ0 : Sym4 (0 :: F.Zt) := Sym4.cons (by simp [ALL]) F.hZ
  have hnA : NoB (MEnc (W.take r) ++ Enc ((n + 1) :: Wr) ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]) ++ MEnc d ++
      List.replicate (0 + r + 1) 2) := by simp [NB]
  have hIL := il0Walk' _ (1 :: (Enc X' ++ 1 :: (F.Hc c ++ 0 :: F.Zt))) hnA (Sym4.cons (by simp [ALL]) hXs)
  have hxs0 : ∀ x ∈ (List.replicate e 2 :: ((d'.map fun e => List.replicate e 2) ++ List.replicate (r + 1) 2 ::
      X'.map fun e => List.replicate e 3)), Bits x ∧ x ≠ [] := by
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨v, hv, rfl⟩ | rfl | ⟨v, hv, rfl⟩
    · exact ⟨bits_rep2 e, by intro h; have := congrArg List.length h; simp at this; omega⟩
    · exact ⟨bits_rep2 v, by have := hd' v hv; intro h; have := congrArg List.length h; simp at this; omega⟩
    · exact ⟨bits_rep2 _, by intro h; have := congrArg List.length h; simp at this⟩
    · exact ⟨bits_rep3 v, by have := hX' v hv; intro h; have := congrArg List.length h; simp at this; omega⟩
  have hCol := colPartU F (W.take r) (Wr.map fun e => List.replicate e 3) (List.replicate e 2)
    ((d'.map fun e => List.replicate e 2) ++ List.replicate (r + 1) 2 :: X'.map fun e => List.replicate e 3) r0
    hms (fun x hx => by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
      exact ⟨bits_rep3 v, by have := hWr v hv; intro h; have := congrArg List.length h; simp at this; omega⟩)
    (hxs0 _ (List.mem_cons_self ..)) (fun x hx => hxs0 x (List.mem_cons_of_mem _ hx)) hr0 (p + 1) n c hc T hTb hT
  have hWL : ∀ x ∈ (W.take r).map (fun e => List.replicate e 2) ++ (List.replicate n 2 ++ [3]) :: Wr.map (fun e => List.replicate e 3),
      Bits x ∧ x ≠ [] := by
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.mem_map] at hx
    rcases hx with ⟨v, hv, rfl⟩ | rfl | ⟨v, hv, rfl⟩
    · exact ⟨bits_rep2 v, by have := hms v hv; intro h; have := congrArg List.length h; simp at this; omega⟩
    · refine ⟨fun a ha => ?_, by simp⟩
      rcases List.mem_append.1 ha with ha | ha
      · rw [List.eq_of_mem_replicate ha]; simp [bits]
      · simp at ha; subst ha; simp [bits]
    · exact ⟨bits_rep3 v, by have := hWr v hv; intro h; have := congrArg List.length h; simp at this; omega⟩
  have nRl : NoB (MEs (List.replicate e 2 :: ((d'.map fun e => List.replicate e 2) ++ List.replicate (r + 1) 2 ::
      X'.map fun e => List.replicate e 3)) ++ 1 :: (MU T ++ [3])) := by
    have := MEs_noB _ (fun x hx => (hxs0 x hx).1)
    simp only [NoB_app_iff, NoB_cons_iff]
    simp [NB, this, MU_noB T hTb]
  have sRr : Sym4 (2 :: (r0 ++ 0 :: F.Zt)) := Sym4.cons (by simp [ALL]) (hr0.app hZ0)
  have hT1 := toY1g _ (List.replicate (p + 1) 3) _ _ hWL (bits_rep3 _) nRl sRr
  have eX : MEs (List.replicate e 2 :: ((d'.map fun e => List.replicate e 2) ++ List.replicate (r + 1) 2 ::
      X'.map fun e => List.replicate e 3)) = MEnc d ++ List.replicate (r + 1) 2 ++ 1 :: Enc X' := by
    subst hdeq
    simp [MEnc_MEs, Enc_MEs, MEs_append, MEs, ME, List.append_assoc]
  rw [eX] at hCol hT1
  refine (hL.of_eq (by simp [MEnc]) rfl).trans ((hIL.of_eq (by simp [Enc, MEnc, List.append_assoc]) rfl).trans
    ((hCol.of_eq (by simp [Enc, U, MEnc, Enc_MEs, List.append_assoc]) rfl).trans (hT1.of_eq ?_ ?_)))
  · simp [MEnc_MEs, MEs_append, MEs, ME, List.append_assoc]
  · have e1 : MEs ((W.take r).map (fun e => List.replicate e 2) ++ (List.replicate n 2 ++ [3]) :: Wr.map (fun e => List.replicate e 3)) =
        MEnc (W.take r) ++ List.replicate n 2 ++ 3 :: 1 :: MEs (Wr.map fun e => List.replicate e 3) := by
      simp [MEnc_MEs, MEs_append, MEs, ME, List.append_assoc]
    have u3 : unm (MEs (Wr.map fun e => List.replicate e 3)) = MEs (Wr.map fun e => List.replicate e 3) := by
      rw [← Enc_MEs, unm_Enc]
    rw [e1, show Enc W = Enc (W.take r) ++ Enc ((n + 1) :: Wr) from by rw [← Enc_append, ← hr, List.take_append_drop]]
    simp [unm_append, unm_rep2, unm_rep3, unm1, unm_MEnc, u3, Enc_MEs, rep3_cons, MEs, ME, MEnc, MEnc_append, Enc, U,
      List.replicate_succ, List.append_assoc]
    done

/-! ### The `H` tape across edges: cutting at one entry -/

def Qof (B : List (List Nat)) : List Nat :=
  match B with
  | [] => []
  | u :: ts => 1 :: HP (u :: ts) 0

theorem HP_cons (a : List Nat) (l : List (List Nat)) (c : Nat) (hl : l ≠ []) :
    HP (a :: l) c = (if 0 < c then 2 else 3) :: (a ++ 1 :: HP l (c - 1)) := by
  cases l with
  | nil => exact absurd rfl hl
  | cons u ts => rfl

theorem HP_cut (t : List Nat) (B : List (List Nat)) : ∀ (A : List (List Nat)),
    HP (A ++ t :: B) A.length = MP A ++ 3 :: (t ++ Qof B) ∧
    HP (A ++ t :: B) 0 = MU A ++ 3 :: (t ++ Qof B)
  | [] => by
    cases B with
    | nil => simp [HP, MP, MU, Qof]
    | cons u ts => simp [HP, MP, MU, Qof]
  | a :: A => by
    obtain ⟨h1, h2⟩ := HP_cut t B A
    have hne : A ++ t :: B ≠ [] := by simp
    refine ⟨?_, ?_⟩
    · rw [List.cons_append, List.length_cons, HP_cons _ _ _ hne]
      simp [MP, h1]
    · rw [List.cons_append, HP_cons _ _ _ hne]
      simp [MU, h2]

/-- The tail (cells after the first) of the `H` entry of value `v`, with the edge used or not. -/
def tl (v : Nat) (b : Bool) : List Nat :=
  if v ≤ 1 then [] else (if b then 2 else 3) :: List.replicate (v - 2) 3

def Hs (H used : List Nat) : List (List Nat) :=
  (List.range H.length).map fun i => tl (H.getD i 0) (decide (i + 1 ∈ used))

theorem Hs_length (H used : List Nat) : (Hs H used).length = H.length := by simp [Hs]

theorem Hs_get (H used : List Nat) (i : Nat) (hi : i < H.length) :
    (Hs H used)[i]'(by rw [Hs_length]; exact hi) = tl (H.getD i 0) (decide (i + 1 ∈ used)) := by
  simp [Hs]

theorem tl_bits (v : Nat) (b : Bool) : Bits (tl v b) := by
  intro a ha
  unfold tl at ha
  split at ha
  · simp at ha
  · rcases List.mem_cons.1 ha with rfl | ha
    · split <;> simp [bits]
    · rw [List.eq_of_mem_replicate ha]; simp [bits]

theorem Hs_bits (H used : List Nat) : ∀ t ∈ Hs H used, Bits t := by
  intro t ht
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 ht
  exact tl_bits _ _

/-- Marking the edge `k` as used rewrites one entry. -/
theorem Hs_mark (H used : List Nat) (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ H.length) (hv : 2 ≤ H.getD (k - 1) 0)
    (hu : k ∉ used) :
    Hs H (k :: used) = (Hs H used).take (k - 1) ++ (2 :: List.replicate (H.getD (k - 1) 0 - 2) 3) :: (Hs H used).drop k := by
  apply List.ext_getElem
  · simp [Hs]; omega
  · intro i h1 h2
    have hiH : i < H.length := by simpa [Hs] using h1
    rw [show (Hs H (k :: used))[i] = tl (H.getD i 0) (decide (i + 1 ∈ k :: used)) from Hs_get _ _ _ hiH]
    rw [List.getElem_append]
    split
    · rename_i hlt
      rw [List.getElem_take, Hs_get _ _ _ hiH]
      have : i + 1 ≠ k := by simp at hlt; omega
      simp [this]
    · rename_i hge
      have hlen : ((Hs H used).take (k - 1)).length = k - 1 := by simp [Hs_length]; omega
      simp only [hlen]
      by_cases hik : i - (k - 1) = 0
      · have hi : i = k - 1 := by omega
        subst hi
        have hv1 : 1 < H.getD (k - 1) 0 := by omega
        rw [List.getD_eq_getElem?_getD] at hv1
        simp [hik, tl, show ¬ (H.getD (k - 1) 0 ≤ 1) by omega, show (k - 1 + 1) = k by omega, hv1]
      · obtain ⟨j, hj⟩ : ∃ j, i - (k - 1) = j + 1 := ⟨i - (k - 1) - 1, by omega⟩
        have e : i = k + j := by omega
        subst e
        simp only [hj, List.getElem_cons_succ, List.getElem_drop]
        rw [Hs_get _ _ _ (by omega)]
        have : k + j + 1 ≠ k := by omega
        simp [this]

/-- Decompose `W` at a position. -/
theorem W_split (W : List Nat) (hW : ∀ e ∈ W, 1 ≤ e) (r : Nat) (hr : r < W.length) :
    ∃ n Wr, W.drop r = (n + 1) :: Wr ∧ W.getD r 0 = n + 1 := by
  have h1 : W.drop r = W[r] :: W.drop (r + 1) := List.drop_eq_getElem_cons hr
  have h2 : 1 ≤ W[r] := hW _ (List.getElem_mem hr)
  refine ⟨W[r] - 1, W.drop (r + 1), ?_, ?_⟩
  · rw [h1]; congr 1; omega
  · rw [List.getD_eq_getElem?_getD]; simp [hr]; omega

/-- One successful edge `(r+1, r'+1)`. -/
theorem edgeStep (W : List Nat) (hW : ∀ e ∈ W, 1 ≤ e) (p : Nat) (H used J Zt : List Nat) (hJ : JShape J) (hZ : Sym4 Zt)
    (hne : H ≠ []) (hHv : ∀ e ∈ H, 1 ≤ e) (d X'' : List Nat) (r r' : Nat)
    (hdd : ∀ e ∈ d, 1 ≤ e) (hX'' : ∀ e ∈ X'', 1 ≤ e) (hdl : d.length % 2 = 0)
    (hr : r < W.length) (hr' : r' < W.length) (k : Nat)
    (hkd : k = (W.getD r 0 - 1) * (p + 1) + W.getD r' 0)
    (hk : k ≤ H.length) (hv : 2 ≤ H.getD (k - 1) 0) (hu : k ∉ used) :
    zgiLogic.Reach
      (hdR QG.gY1e (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]))
        (MEnc d ++ List.replicate (r + 1) 3 ++ 1 :: (Enc ((r' + 1) :: X'') ++ 1 :: (HP (Hs H used) 0 ++ J ++ 0 :: Zt))))
      (hdR QG.gY1e (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]))
        (MEnc (d ++ [r + 1, r' + 1]) ++ Enc X'' ++ 1 :: (HP (Hs H (k :: used)) 0 ++ J ++ 0 :: Zt))) := by
  obtain ⟨n, Wr, hdr, hgr⟩ := W_split W hW r hr
  obtain ⟨n', Wr', hdr', hgr'⟩ := W_split W hW r' hr'
  have hk1 : 1 ≤ k := by
    rw [hkd, hgr']; exact Nat.le_trans (Nat.succ_le_succ (Nat.zero_le n')) (Nat.le_add_left _ _)
  have hkn : k = n * (p + 1) + n' + 1 := by rw [hkd, hgr, hgr']; simp [Nat.add_assoc]
  have hmul : (p + 1) * n = n * (p + 1) := Nat.mul_comm _ _
  have hhne : Hs H used ≠ [] := by
    intro h; have := Hs_length H used; rw [h] at this; simp at this; exact hne (List.length_eq_zero_iff.1 this.symm)
  let F := HFam.ofHP (Hs H used) hhne (Hs_bits H used) J hJ Zt hZ
  have hFN : F.N = H.length := by simp [F, HFam.ofHP, Hs_length]
  have hFc : ∀ c, F.Hc c = HP (Hs H used) c ++ J := fun c => rfl
  have hFZ : F.Zt = Zt := rfl
  have hX' : ∀ e ∈ (r' + 1) :: X'', 1 ≤ e := by
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · omega
    · exact hX'' e he
  have hrow := rowHalf F W Wr d ((r' + 1) :: X'') r n p 0 hW hdd hX' hdl hdr (by omega)
    (by rw [hFN]; omega)
  have hlt : k - 1 < H.length := by omega
  have hget : (Hs H used)[k - 1]'(by rw [Hs_length]; exact hlt) = 3 :: List.replicate (H.getD (k - 1) 0 - 2) 3 := by
    rw [Hs_get _ _ _ hlt]
    have : (k - 1 + 1) = k := by omega
    have hv1 : 1 < H.getD (k - 1) 0 := by omega
    rw [List.getD_eq_getElem?_getD] at hv1
    simp [tl, this, hu, show ¬ (H.getD (k - 1) 0 ≤ 1) by omega, hv1]
  have hsplit : Hs H used = (Hs H used).take (k - 1) ++ (3 :: List.replicate (H.getD (k - 1) 0 - 2) 3) :: (Hs H used).drop k := by
    have e0 := List.take_append_drop (k - 1) (Hs H used)
    have h1 : (Hs H used).drop (k - 1) = (Hs H used)[k - 1]'(by rw [Hs_length]; exact hlt) :: (Hs H used).drop (k - 1 + 1) :=
      List.drop_eq_getElem_cons (by rw [Hs_length]; exact hlt)
    rw [h1, hget, show k - 1 + 1 = k by omega] at e0
    exact e0.symm
  obtain ⟨A, hA⟩ : ∃ A, A = (Hs H used).take (k - 1) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = (Hs H used).drop k := ⟨_, rfl⟩
  obtain ⟨rr, hrr⟩ : ∃ rr, rr = List.replicate (H.getD (k - 1) 0 - 2) 3 := ⟨_, rfl⟩
  rw [← hA, ← hB, ← hrr] at hsplit
  have hAl : A.length = k - 1 := by rw [hA]; simp [Hs_length]; omega
  have hBits : ∀ t ∈ B, Bits t := fun t ht => Hs_bits H used t (List.mem_of_mem_drop (hB ▸ ht))
  have hAb : ∀ t ∈ A, Bits t := fun t ht => Hs_bits H used t (List.mem_of_mem_take (hA ▸ ht))
  have sQB : Sym4 (Qof B) := by
    cases B with
    | nil => simp [Qof, ALL]
    | cons u ts => exact Sym4.cons (by simp [ALL]) (HP_sym4 _ _ hBits)
  have sr0 : Sym4 (rr ++ Qof B ++ J) := by
    refine ((((hrr ▸ bits_rep3 _ : Bits rr)).sym4).app sQB).app hJ.1.sym4
  obtain ⟨hc1, hc2⟩ := HP_cut (3 :: rr) B A
  rw [← hsplit] at hc1 hc2
  have hT : F.Hc ((p + 1) * n + n') = MP A ++ 3 :: 3 :: (rr ++ Qof B ++ J) := by
    rw [hFc, show (p + 1) * n + n' = A.length by omega, hc1]; simp
  have hcol := colHalf F W Wr' (d ++ [r + 1]) X'' r' n' p ((p + 1) * n) A (rr ++ Qof B ++ J) hW
    (by intro e he; rcases List.mem_append.1 he with he | he
        · exact hdd e he
        · simp at he; omega) hX'' (by simp; omega) hdr' (by rw [hFN]; omega) hAb hT sr0
  have hmark := Hs_mark H used k hk1 hk hv hu
  rw [← hA, ← hB, ← hrr] at hmark
  refine (hrow.of_eq (by simp [Enc, U, List.append_assoc, hFc, hFZ]) rfl).trans (hcol.of_eq (by simp [Enc, U, List.append_assoc, hFc, hFZ]) ?_)
  rw [hmark]
  have hc3 := (HP_cut (2 :: rr) B A).2
  rw [hc3]
  simp [List.append_assoc, hFZ]

end ZP.G
