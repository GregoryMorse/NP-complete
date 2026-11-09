module

public import ZP.GenStep
public import ZP.CompileNTT
public import ZP.EvalNTT
public import ZP.PrimeNTT
public import ZP.AbstractNTT
public import ZP.PairF

@[expose] public section

/-!
# The NTT machine quasihalts iff `SentenceN primeN` (under `PrimeEx`)

`layNTT c n` is the pair start (`PA0`, `P = 1`, `K = 3`, `C = c`, `Nn = n`). `pair_ntt` composes the prime
ruler, the record build, the assignment loop and its two continuations. `PairDataN` along the abstract
trajectory `absN` then gives the macro simulation and the headline theorem.
-/

namespace ZP.NTT

open ZP

/-- Record list: digits `O`, pointer range `i+1, i+2, …`. -/
def mkPs : List Nat → Nat → List (Nat × Nat)
  | [], _ => []
  | O :: Os, i => (O, i + 1) :: mkPs Os (i + 1)

theorem mkPs_len : ∀ Os i, (mkPs Os i).length = Os.length
  | [], _ => rfl
  | _ :: Os, i => by simp [mkPs, mkPs_len Os (i + 1)]

theorem mkPs_append : ∀ (A B : List Nat) (i : Nat), mkPs (A ++ B) i = mkPs A i ++ mkPs B (i + A.length)
  | [], B, i => by simp [mkPs]
  | O :: A, B, i => by
    simp only [List.cons_append, mkPs, List.length_cons]
    rw [mkPs_append A B (i + 1)]
    rw [show i + 1 + A.length = i + (A.length + 1) by omega]

theorem resetO_mkPs : ∀ (Os : List Nat) (i : Nat), resetO (mkPs Os i) = mkPs (List.replicate Os.length 2) i
  | [], _ => rfl
  | O :: Os, i => by
    simp only [resetO, mkPs, List.map_cons, List.length_cons, List.replicate_succ] at *
    rw [show (List.map (fun q => (2, q.2)) (mkPs Os (i + 1))) = resetO (mkPs Os (i + 1)) from rfl,
      resetO_mkPs Os (i + 1)]

theorem newRecs_mkPs : ∀ (u w : Nat), newRecs (w + 1) u = mkPs (List.replicate u 3) w
  | 0, _ => rfl
  | u + 1, w => by
    simp only [newRecs, mkPs, List.replicate_succ]
    rw [newRecs_mkPs u (w + 1)]

theorem roundsPs_mk (n : Nat) : ∀ (c : Nat) (Os : List Nat) (i w0 : Nat), w0 = i + Os.length + 1 →
    roundsPs n c w0 (mkPs Os i) =
      mkPs (if c = 0 then Os else List.replicate (Os.length + (c - 1) * (n + 1)) 2 ++ List.replicate (n + 1) 3) i
  | 0, Os, i, w0, _ => by simp [roundsPs]
  | c + 1, Os, i, w0, hw => by
    subst hw
    simp only [roundsPs]
    rw [resetO_mkPs, newRecs_mkPs]
    have hap := mkPs_append (List.replicate Os.length 2) (List.replicate (n + 1) 3) i
    simp only [List.length_replicate] at hap
    rw [← hap]
    have ih := roundsPs_mk n c (List.replicate Os.length 2 ++ List.replicate (n + 1) 3) i
      (i + Os.length + 1 + (n + 1)) (by simp; omega)
    rw [ih]
    congr 1
    by_cases hc : c = 0
    · subst hc; simp
    · simp only [hc, if_false, if_neg (Nat.succ_ne_zero c)]
      simp only [List.length_append, List.length_replicate]
      rw [show Os.length + (n + 1) + (c - 1) * (n + 1) = Os.length + (c + 1 - 1) * (n + 1) by
        obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        rw [Nat.add_mul]; omega]

theorem initFrom_mkPs (p : Nat) : ∀ (Os : List Nat) (i : Nat), (mkPs Os i).map (recO (p - 1)) = initFrom p i Os
  | [], _ => rfl
  | O :: Os, i => by simp [mkPs, initFrom, initFrom_mkPs p Os (i + 1)]


def layNTT (c n : Nat) : ZC :=
  hdR QNTT.PA0 [3] (1 :: (List.replicate 3 3 ++ 1 :: (List.replicate c 3 ++ 1 :: List.replicate n 3)))

theorem zntt_h0 : znttLogic.zconf 20 = some (layNTT 1 1) := by
  rfl

theorem hdR_pad (q : Nat) (A R : List Nat) (z : Nat) : hdR q A (R ++ List.replicate z 0) = hdR q A R := by
  rw [F.hdR_eq', F.hdR_eq', sapp_append, F.sapp_zeros]

theorem hd_eq' (q : Nat) (A R : List Nat) :
    hd q A R = ⟨q, stail (sapp A.reverse blank), scons (sapp A.reverse blank 0) (sapp R blank)⟩ := by
  show (⟨q, stail (sapp (dL [A, R] [.blk 0 .id]) blank),
    scons (sapp (dL [A, R] [.blk 0 .id]) blank 0) (sapp (dR [A, R] [.blk 1 .id]) blank)⟩ : ZC) = _
  rw [dW_blk0, dW_blk1]

theorem hd_pad (q : Nat) (A R : List Nat) (z : Nat) : hd q A (R ++ List.replicate z 0) = hd q A R := by
  rw [hd_eq', hd_eq', sapp_append, F.sapp_zeros]

theorem primeN_ge (hex : PrimeEx) (n : Nat) (hn : 1 ≤ n) : 2 ≤ primeN n := by
  obtain ⟨i, hi1, hi2⟩ := hex n hn
  obtain ⟨i1, _, hp1, hpn, _⟩ := primeN_spec n ⟨i, hi1, hi2⟩
  rw [hpn]
  unfold isPrimeN at hp1
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp1
  exact hp1.1

/-- Setup shared by both outcomes: prime ruler, record build. -/
theorem pair_front (hex : PrimeEx) (c n : Nat) (hc : 1 ≤ c) (hn : 1 ≤ n) :
    ∃ (j nb : Nat) (o : ORec) (os : List ORec) (Os : List Nat),
      j + 1 = primeN n ∧ nb + 1 = n ∧ 2 ≤ j + 1 ∧ Os.length = c * n ∧
      Os = List.replicate (c * n - n) 2 ++ List.replicate n 3 ∧ initFrom (j + 1) 0 Os = o :: os ∧
      znttLogic.Reach1 (layNTT c n)
        (loopSt (List.replicate (wEnd nb c 1 + 1) 3) (List.replicate 3 3) (List.replicate c 3) nb (j + 1) o os) := by
  have hp2 := primeN_ge hex n hn
  obtain ⟨j, hj⟩ : ∃ j, primeN n = j + 1 := ⟨primeN n - 1, by omega⟩
  obtain ⟨nb, hnb⟩ : ∃ nb, n = nb + 1 := ⟨n - 1, by omega⟩
  have hM : NoB (List.replicate 3 3 ++ 1 :: List.replicate c 3) := by
    simp [NB]
  have h1 := primeRuler_primeN hex n hn _ [] hM (by intro a ha; simp at ha)
  have h1' : znttLogic.Reach1 (layNTT c n)
      (hd QNTT.WX [0, 3] (1 :: (List.replicate (j + 1) 3 ++ 1 :: (List.replicate (2 + 1) 3 ++ 1 ::
        (List.replicate c 3 ++ 1 :: List.replicate (nb + 1) 3))))) := by
    refine F.Reach_pos (h1.of_eq ?_ ?_) (by simp only [layNTT, hdR, hd, SC.den_q]; decide)
    · simp only [layNTT, List.replicate_zero, List.nil_append]
      have := hdR_pad QNTT.PA0 [3] (1 :: (List.replicate 3 3 ++ 1 :: (List.replicate c 3 ++ 1 :: List.replicate n 3))) 1
      simp only [List.replicate_succ, List.replicate_zero] at this
      rw [show List.replicate 1 3 = [3] from rfl]
      simp only [List.cons_append, List.append_assoc, List.nil_append] at this ⊢
      exact this
    · rw [hj, ← hnb]
      have := hd_pad QNTT.WX [0, 3] (1 :: (List.replicate (j + 1) 3 ++ 1 :: (List.replicate (2 + 1) 3 ++ 1 ::
        (List.replicate c 3 ++ 1 :: List.replicate n 3)))) 1
      rw [hnb] at this ⊢
      simp only [List.replicate_succ, List.replicate_zero, List.cons_append, List.append_assoc, List.nil_append] at this ⊢
      exact this
  obtain ⟨o, os, hos, hb⟩ := buildEntry j c nb (by omega) (by omega)
  have hrp := roundsPs_mk nb c [] 0 1 (by simp)
  have hmk : mkPs [] 0 = [] := rfl
  rw [hmk, if_neg (by omega)] at hrp
  have hcn : (c - 1) * (nb + 1) = c * n - n := by
    rw [hnb, Nat.sub_mul, Nat.one_mul]
  have hOs : List.replicate (([] : List Nat).length + (c - 1) * (nb + 1)) 2 ++ List.replicate (nb + 1) 3 =
      List.replicate (c * n - n) 2 ++ List.replicate n 3 := by
    rw [List.length_nil, Nat.zero_add, hcn, hnb]
  have hif := initFrom_mkPs (j + 1) (List.replicate (c * n - n) 2 ++ List.replicate n 3) 0
  rw [Nat.add_sub_cancel] at hif
  rw [hrp, hOs, hif] at hos
  have hlenO : (List.replicate (c * n - n) 2 ++ List.replicate n 3).length = c * n := by
    simp only [List.length_append, List.length_replicate]
    have : n ≤ c * n := Nat.le_mul_of_pos_left n (by omega)
    omega
  refine ⟨j, nb, o, os, _, hj.symm ▸ rfl, hnb.symm, by omega, hlenO, rfl, hos.symm, ?_⟩
  refine h1'.trans ?_
  refine hb.of_eq rfl ?_
  simp only [loopSt, Pfx, NnTail, List.append_assoc, List.replicate_zero, List.nil_append, List.cons_append,
    Nat.zero_add, List.append_nil]

theorem znttBeep : znttLogic.beep = QNTT.BEEP := by decide

/-- The pair lemma of the NTT machine. -/
theorem pair_ntt (hex : PrimeEx) (c n : Nat) (hc : 1 ≤ c) (hn : 1 ≤ n) :
    ∃ k, 0 < k ∧ znttLogic.Seg (layNTT c n) k
      (layNTT (ZP.stepN primeN (c, n)).1 (ZP.stepN primeN (c, n)).2) (¬ hasCircuit primeN c n = true) := by
  obtain ⟨j, nb, o, os, Os, hjp, hnb, hj2, hOl, hOs, ho, hr⟩ := pair_front hex c n hc hn
  have hcn1 : 1 ≤ c * n := Nat.mul_pos hc hn
  have hlen : os.length = c * n - 1 := by
    have := congrArg List.length ho
    rw [initFrom_len] at this
    simp at this; omega
  have hOl' : Os.length = c * n - 1 + 1 := by omega
  have hOs' : Os = List.replicate (c * n - 1 + 1 - n) 2 ++ List.replicate n 3 := by
    rw [Nat.sub_add_cancel hcn1]; exact hOs
  have hnrN : n ≤ c * n - 1 + 1 := by
    have : n ≤ c * n := Nat.le_mul_of_pos_left n (by omega)
    omega
  have key := assign_circuit primeN c n (c * n - 1) (j + 1) Os hjp.symm (by omega) hj2 hn hnrN hOl' hOs'
    (wEnd nb c 1 + 1) 3 c (by omega) hc o os ho hlen
  subst hnb
  simp only [Nat.add_sub_cancel] at key
  rcases key with ⟨hcF, A, n0, hreach, X, hX, hrX⟩ | ⟨hcT, D, N, T, hs, h1, h2⟩
  · have hstep : ZP.stepN primeN (c, nb + 1) = (c + 1, nb + 1) := by
      unfold ZP.stepN; simp [hcF]
    rw [hstep]
    obtain ⟨a, ha⟩ := hr.trans hreach
    have e1 : hdR QNTT.PA0 [3]
        (1 :: (List.map (fun x => if x = 1 then 1 else 3) (List.replicate 3 3) ++
          1 :: (List.map (fun x => if x = 1 then 1 else 3) (List.replicate c 3) ++ [3] ++
            1 :: (List.replicate (nb + 1 + 0) 3 ++ List.replicate (n0 + 1) 0)))) = layNTT (c + 1) (nb + 1) := by
      have := hdR_pad QNTT.PA0 [3] (1 :: (List.replicate 3 3 ++ 1 :: (List.replicate (c + 1) 3 ++ 1 :: List.replicate (nb + 1) 3))) (n0 + 1)
      unfold layNTT
      rw [← this]
      congr 1
      simp [List.replicate_succ', List.map_replicate, List.append_assoc]
    obtain ⟨m, hm⟩ := hrX.of_eq rfl e1
    refine ⟨a + 1 + 1 + m, by omega, fun h => absurd (by simp [hcF]) h, fun _ => ⟨a + 1, hd QNTT.BEEP A [], X, by omega, ha, ?_, hX, ?_⟩⟩
    · simp only [hd, SC.den_q]; exact znttBeep.symm
    · rw [show a + 1 + 1 + m - (a + 1) - 1 = m by omega]; exact hm
  · have hstep : ZP.stepN primeN (c, nb + 1) = (c, nb + 1 + 1) := by
      unfold ZP.stepN; simp [hcT]
    rw [hstep]
    obtain ⟨m, hm⟩ := (hr.trans h1).trans h2
    have e1 : hdR QNTT.PA0 [3] (1 :: (List.replicate 3 3 ++ 1 :: (List.replicate c 3 ++ 1 ::
        (List.replicate (0 + nb + 1 + 1) 3 ++ List.replicate (N + 1) 0)))) = layNTT c (nb + 1 + 1) := by
      have := hdR_pad QNTT.PA0 [3] (1 :: (List.replicate 3 3 ++ 1 :: (List.replicate c 3 ++ 1 :: List.replicate (nb + 1 + 1) 3))) (N + 1)
      unfold layNTT
      rw [← this]
      congr 1
      simp [List.append_assoc]
    rw [e1] at hm
    exact ⟨m + 1, by omega, fun _ => hm, fun h => absurd hcT h⟩


/-- Pair data of `znttLogic` along the abstract trajectory. -/
noncomputable def zntPairData (hex : PrimeEx) :
    PairDataN znttLogic (fun k => ¬ hasCircuit primeN (absN primeN k).1 (absN primeN k).2 = true) where
  lay k := layNTT (absN primeN k).1 (absN primeN k).2
  k0 := 20
  h0 := zntt_h0
  step k := by
    obtain ⟨hc, hn⟩ := absN_inv primeN k
    exact pair_ntt hex _ _ hc hn

theorem znttLogic_macroSim (hex : PrimeEx) :
    Nonempty (LMacroSimB (fun k => ¬ hasCircuit primeN (absN primeN k).1 (absN primeN k).2 = true) znttLogic) :=
  (zntPairData hex).macroSim

theorem znttQuasihalts_iff_abstract (hex : PrimeEx) : Quasihalts znttMachine ↔ AbstractQN primeN :=
  match znttLogic_macroSim hex with
  | ⟨S⟩ =>
    (quasihalts_iff_of_macroSimB (Cert.macroSimB_of_logic znttCert znttCert_ok S)).trans
      (by unfold AbstractQN; simp only [Classical.not_not])

/-- Headline theorem for plan 08 (`PrimeEx` is the stated hypothesis). -/
theorem znttQuasihalts_iff_sentence (hex : PrimeEx) : Quasihalts znttMachine ↔ SentenceN primeN :=
  (znttQuasihalts_iff_abstract hex).trans (sentenceN_iff hex)

end ZP.NTT
