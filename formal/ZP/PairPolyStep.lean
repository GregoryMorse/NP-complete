module

public import ZP.PairPolyPair
public import ZP.AbstractPoly
public import ZP.ReducePoly

@[expose] public section

/-!
# One abstract step, simulated

`layPoly st` is the configuration of the state `st = (K, n, A, v)`; one `polyStep` is one
run of the logical machine, visiting the beep state iff `polyOver st`, and then once.
-/

namespace ZP.Poly

open ZP

/-- The configuration of the abstract state `st`: `M_g rev(K) M_1 a M_a s`. -/
def layPoly (st : PSt) : ZC :=
  layP (bitsOf (str st.K).reverse) (bitsOf (str st.A)) (bitsOf (svec st.n st.v))

theorem layP_q (Kr a s : List Nat) : (layP Kr a s).q = Q.GRB := by
  unfold layP
  rw [hdR_eqP]

theorem LTM.Reach.seg_pos {L : LTM} {c m d : ZC} (h1 : L.Reach c m) (hq : c.q ≠ m.q)
    (h2 : L.Reach m d) : ∃ n, 0 < n ∧ L.zrun n c = some d := by
  obtain ⟨n1, hn1⟩ := h1
  obtain ⟨n2, hn2⟩ := h2
  cases n1 with
  | zero =>
    have : c = m := Option.some.inj hn1
    exact absurd (by rw [this]) hq
  | succ n1 =>
    refine ⟨n1 + 1 + n2, by omega, ?_⟩
    rw [LTM.zrun_add, hn1]
    exact hn2


/-! ## Counters -/

theorem ofBv_next : ∀ n v : Nat, v + 1 < 2 ^ n →
    false ∈ ofBv n v ∧ incR (ofBv n v) = ofBv n (v + 1)
  | 0, v, h => by simp at h
  | n + 1, v, h => by
    have hp : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ _ _
    by_cases hm : v % 2 = 1
    · have hlt : v / 2 + 1 < 2 ^ n := by omega
      obtain ⟨h1, h2⟩ := ofBv_next n (v / 2) hlt
      have e1 : (v + 1) % 2 = 0 := by omega
      have e2 : (v + 1) / 2 = v / 2 + 1 := by omega
      refine ⟨?_, ?_⟩
      · simp [ofBv, hm, h1]
      · simp [ofBv, hm, incR, h2, e1, e2]
    · have hm0 : v % 2 = 0 := by omega
      have e1 : (v + 1) % 2 = 1 := by omega
      have e2 : (v + 1) / 2 = v / 2 := by omega
      refine ⟨?_, ?_⟩
      · simp [ofBv, hm]
      · simp [ofBv, hm, incR, e1, e2]

theorem ofBv_carry : ∀ n v : Nat, v + 1 = 2 ^ n → ∀ x ∈ ofBv n v, x = true
  | 0, v, _ => by simp [ofBv]
  | n + 1, v, h => by
    have hp : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ _ _
    have hm : v % 2 = 1 := by omega
    have hd : v / 2 + 1 = 2 ^ n := by omega
    have := ofBv_carry n (v / 2) hd
    intro x hx
    simp only [ofBv, List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp [hm]
    · exact this x hx

theorem ofBv_zero : ∀ n, ofBv n 0 = List.replicate n false
  | 0 => rfl
  | n + 1 => by simp [ofBv, ofBv_zero n, List.replicate_succ]

theorem svec_zero (n : Nat) : svec n 0 = List.replicate n false := by
  simp [svec, ofBv_zero]

theorem svec_succ_eq (n v : Nat) : svec n v = (ofBv n v).reverse := rfl

/-! ## Numerals -/

theorem nums (st : PSt) (hK : 1 ≤ st.K) (hA : 1 ≤ st.A) :
    ∃ rK rA : List Bool, str st.K = rK.reverse ∧ str st.A = rA.reverse ∧
      str (st.K + 1) = (incR rK).reverse ∧ str (st.A + 1) = (incR rA).reverse := by
  obtain ⟨rK, hrK⟩ := numR_surj st.K hK
  obtain ⟨rA, hrA⟩ := numR_surj st.A hA
  refine ⟨rK, rA, ?_, ?_, ?_, ?_⟩
  · rw [← hrK, str_numR]
  · rw [← hrA, str_numR]
  · rw [← hrK, ← numR_inc, str_numR]
  · rw [← hrA, ← numR_inc, str_numR]

/-! ## The three outcomes -/

theorem front (Kr a : List Nat) (hKr : Bits Kr) (ha : Bits a) (Sb : List Bool) :
    ∃ m : ZC, m.q ≠ Q.GRB ∧ zppolyLogic.Reach (layP Kr a (bitsOf Sb)) m ∧
      zppolyLogic.Reach m (TR Kr a Sb (inL Sb)) :=
  ⟨_, by unfold GCv; rw [hdR_eqP]; show Q.GC ≠ Q.GRB; decide, vStart Kr a hKr ha Sb,
    vFull Kr a hKr ha Sb⟩

theorem layPoly_eq (st : PSt) (rK rA : List Bool) (eK : str st.K = rK.reverse)
    (eA : str st.A = rA.reverse) :
    layPoly st = layP (bitsOf rK) (bitsOf rA.reverse) (bitsOf (svec st.n st.v)) := by
  unfold layPoly
  rw [eK, eA, List.reverse_reverse]

theorem budget_eq (st : PSt) (rK : List Bool) (eK : str st.K = rK.reverse) :
    (( svec st.n st.v).length + 2) ^ ((bitsOf rK).length + 1) - 1 = bud st.K st.n := by
  simp [bud, budget, svec_length, bitsOf_len, eK]


theorem bitsOf_rep (k : Nat) : bitsOf (List.replicate k false) = List.replicate k 2 := by
  simp [bitsOf, List.map_replicate]

theorem pre (st : PSt) (hK : 1 ≤ st.K) (hA : 1 ≤ st.A) (hno : ¬ polyOver st) :
    ∃ rK rA : List Bool, str st.K = rK.reverse ∧ str st.A = rA.reverse ∧
      str (st.K + 1) = (incR rK).reverse ∧ str (st.A + 1) = (incR rA).reverse ∧
      ∃ m : ZC, m.q ≠ Q.GRB ∧ zppolyLogic.Reach (layPoly st) m ∧ ∃ Fu : List Nat, NoB Fu ∧
        zppolyLogic.Reach m
          (hdR (dpOf (bn (run (str st.A) (svec st.n st.v) (bud st.K st.n - (str st.A).length))))
            [1] (bitsOf rK ++ 1 :: (bitsOf (str st.A) ++ 1 :: (bitsOf (svec st.n st.v) ++
              1 :: 1 :: (tflag (inL (svec st.n st.v)) ++ 1 :: Fu))))) := by
  obtain ⟨rK, rA, eK, eA, eK1, eA1⟩ := nums st hK hA
  refine ⟨rK, rA, eK, eA, eK1, eA1, ?_⟩
  have hKr : Bits (bitsOf rK) := Bits.ofB rK
  have ha : Bits (bitsOf (str st.A)) := Bits.ofB _
  have hs : Bits (bitsOf (svec st.n st.v)) := Bits.ofB _
  have e0 : layPoly st = layP (bitsOf rK) (bitsOf (str st.A)) (bitsOf (svec st.n st.v)) := by
    unfold layPoly; rw [eK, List.reverse_reverse]
  rw [e0]
  obtain ⟨m, hm, h1, h2⟩ := front (bitsOf rK) (bitsOf (str st.A)) hKr ha (svec st.n st.v)
  have hle : (str st.A).length ≤ ((svec st.n st.v).length + 2) ^ ((bitsOf rK).length + 1) - 1 := by
    rw [budget_eq st rK eK]
    exact Nat.not_lt.mp hno
  obtain ⟨Fu, hFu, hR⟩ := (decRun (bitsOf rK) (str st.A) (svec st.n st.v)
    (inL (svec st.n st.v)) hKr).1 hle
  rw [budget_eq st rK eK] at hR
  exact ⟨m, hm, h1, Fu, hFu, h2.trans hR⟩

theorem run_ok (st : PSt) (hno : ¬ polyOver st) (hok : okv st.K st.n st.A st.v) :
    run (str st.A) (svec st.n st.v) (bud st.K st.n - (str st.A).length) =
      inL (svec st.n st.v) := by
  have h := hok
  unfold okv prun at h
  rwa [if_pos (Nat.not_lt.mp hno)] at h

theorem run_bad (st : PSt) (hno : ¬ polyOver st) (hok : ¬ okv st.K st.n st.A st.v) :
    run (str st.A) (svec st.n st.v) (bud st.K st.n - (str st.A).length) =
      !inL (svec st.n st.v) := by
  have h : ¬ (run (str st.A) (svec st.n st.v) (bud st.K st.n - (str st.A).length) =
      inL (svec st.n st.v)) := by
    intro h2
    apply hok
    unfold okv prun
    rw [if_pos (Nat.not_lt.mp hno)]
    exact h2
  revert h
  cases run (str st.A) (svec st.n st.v) (bud st.K st.n - (str st.A).length) <;>
    cases inL (svec st.n st.v) <;> simp

theorem reachOk (st : PSt) (hK : 1 ≤ st.K) (hA : 1 ≤ st.A) (hv : st.v < 2 ^ st.n)
    (hno : ¬ polyOver st) (hok : okv st.K st.n st.A st.v) :
    ∃ m : ZC, m.q ≠ Q.GRB ∧ zppolyLogic.Reach (layPoly st) m ∧
      zppolyLogic.Reach m (layPoly (polyStep st)) := by
  obtain ⟨rK, rA, eK, eA, eK1, eA1, m, hm, h1, Fu, hFu, hR⟩ := pre st hK hA hno
  refine ⟨m, hm, h1, ?_⟩
  rw [run_ok st hno hok] at hR
  have hD := dispOk (bitsOf rK) (bitsOf (str st.A)) (bitsOf (svec st.n st.v)) Fu
    (Bits.ofB _) (Bits.ofB _) (Bits.ofB _) hFu (inL (svec st.n st.v))
  have hS := hR.trans hD
  have e0 : layPoly st = layP (bitsOf rK) (bitsOf (str st.A)) (bitsOf (svec st.n st.v)) := by
    unfold layPoly; rw [eK, List.reverse_reverse]
  by_cases hv1 : st.v + 1 < 2 ^ st.n
  · obtain ⟨hf, hi⟩ := ofBv_next st.n st.v hv1
    have := correctNext (bitsOf rK) (bitsOf (str st.A)) (Bits.ofB _) (Bits.ofB _) (ofBv st.n st.v) hf
    rw [polyStep_next hno hok hv1]
    have e1 : layPoly ⟨st.K, st.n, st.A, st.v + 1⟩ =
        layP (bitsOf rK) (bitsOf (str st.A)) (bitsOf (incR (ofBv st.n st.v)).reverse) := by
      unfold layPoly
      rw [eK, List.reverse_reverse, hi]
      rfl
    rw [e1]
    exact hS.trans (by simpa [svec] using this)
  · have hv2 : st.v + 1 = 2 ^ st.n := by omega
    have hc := ofBv_carry st.n st.v hv2
    have := correctCarry (bitsOf rK) (bitsOf (str st.A)) (Bits.ofB _) (Bits.ofB _) (ofBv st.n st.v) hc
    rw [polyStep_carry hno hok hv1]
    have e1 : layPoly ⟨st.K, st.n + 1, 1, 0⟩ =
        layP (bitsOf rK) [] (List.replicate ((ofBv st.n st.v).length + 1) 2) := by
      unfold layPoly
      rw [eK, List.reverse_reverse, str_one, svec_zero, bitsOf_rep, length_ofBv]
      rfl
    rw [e1]
    exact hS.trans (by simpa [svec] using this)

theorem reachWrong (st : PSt) (hK : 1 ≤ st.K) (hA : 1 ≤ st.A) (hv : st.v < 2 ^ st.n)
    (hno : ¬ polyOver st) (hok : ¬ okv st.K st.n st.A st.v) :
    ∃ m : ZC, m.q ≠ Q.GRB ∧ zppolyLogic.Reach (layPoly st) m ∧
      zppolyLogic.Reach m (layPoly (polyStep st)) := by
  obtain ⟨rK, rA, eK, eA, eK1, eA1, m, hm, h1, Fu, hFu, hR⟩ := pre st hK hA hno
  refine ⟨m, hm, h1, ?_⟩
  rw [run_bad st hno hok] at hR
  have hD := dispWrong (bitsOf rK) (bitsOf (str st.A)) (bitsOf (svec st.n st.v)) Fu
    (Bits.ofB _) (Bits.ofB _) (Bits.ofB _) hFu (inL (svec st.n st.v))
  have hD' : zppolyLogic.Reach m (hd QPoly.ZS (1 :: (bitsOf rK ++ 1 :: (bitsOf (str st.A) ++ 1 :: bitsOf (svec st.n st.v)))) []) := by
    simpa using hR.trans hD
  have hz := zsSweep (1 :: (bitsOf rK ++ 1 :: bitsOf (str st.A))) (bitsOf (svec st.n st.v))
    (by exact (NoB.cons one_nb ((Bits.ofB rK).noB.app (NoB.cons one_nb (Bits.ofB _).noB))).sym4)
    (Bits.ofB _)
  have hw := wrongStep (bitsOf rK) (Bits.ofB _) rA st.n
  rw [polyStep_wrong hno hok]
  have e1 : layPoly ⟨st.K, st.n, st.A + 1, 0⟩ =
      layP (bitsOf rK) (bitsOf (incR rA).reverse) (List.replicate st.n 2) := by
    unfold layPoly
    rw [eK, List.reverse_reverse]
    show layP (bitsOf rK) (bitsOf (str (st.A + 1))) (bitsOf (svec st.n 0)) = _
    rw [eA1, svec_zero, bitsOf_rep]
  rw [e1]
  have hz' : zppolyLogic.Reach (hd QPoly.ZS (1 :: (bitsOf rK ++ 1 :: (bitsOf (str st.A) ++ 1 :: bitsOf (svec st.n st.v)))) [])
      (hd Q.SINC (1 :: (bitsOf rK ++ 1 :: bitsOf (str st.A))) (1 :: List.replicate st.n 2)) := by
    simpa [bitsOf_len, svec_length] using hz
  rw [eA] at hD' hz'
  exact hD'.trans (hz'.trans hw)


theorem reachOver (st : PSt) (hK : 1 ≤ st.K) (hA : 1 ≤ st.A) (ho : polyOver st) :
    ∃ c1 c2 : ZC, zppolyLogic.Reach (layPoly st) c1 ∧ c1.q = zppolyLogic.beep ∧
      zppolyLogic.zstep c1 = some c2 ∧ zppolyLogic.Reach c2 (layPoly (polyStep st)) := by
  obtain ⟨rK, rA, eK, eA, eK1, eA1⟩ := nums st hK hA
  have hKr : Bits (bitsOf rK) := Bits.ofB rK
  have ha : Bits (bitsOf (str st.A)) := Bits.ofB _
  have hs : Bits (bitsOf (svec st.n st.v)) := Bits.ofB _
  have e0 : layPoly st = layP (bitsOf rK) (bitsOf (str st.A)) (bitsOf (svec st.n st.v)) := by
    unfold layPoly; rw [eK, List.reverse_reverse]
  rw [e0]
  obtain ⟨m, hm, h1, h2⟩ := front (bitsOf rK) (bitsOf (str st.A)) hKr ha (svec st.n st.v)
  have hlt : ((svec st.n st.v).length + 2) ^ ((bitsOf rK).length + 1) - 1 < (str st.A).length := by
    rw [budget_eq st rK eK]; exact ho
  obtain ⟨ds1, hR⟩ := (decRun (bitsOf rK) (str st.A) (svec st.n st.v)
    (inL (svec st.n st.v)) hKr).2 hlt
  rw [hdR_zeros_left] at hR
  have ht := tflag_t3 (inL (svec st.n st.v))
  have hY : NoB (bitsOf (str st.A) ++ 1 :: (bitsOf (svec st.n st.v) ++ 1 :: 1 ::
      (tflag (inL (svec st.n st.v)) ++ 1 :: FWr (svec st.n st.v).length ds1))) :=
    ha.noB.app (NoB.cons one_nb (hs.noB.app (NoB.cons one_nb (NoB.cons one_nb
      ((t3_noB ht).app (NoB.cons one_nb (FWr_noB _ _)))))))
  obtain ⟨c2, hc2, hr2⟩ := beepK rK [1] _ (Sym4.cons (by simp [ALL]) Sym4.nil) hY (by simp)
  have e1 : layPoly (polyStep st) = hdR Q.GRB ([1] ++ (bitsOf (incR rK) ++ [1, 1])) [] := by
    rw [polyStep_over ho]
    unfold layPoly
    rw [eK1, List.reverse_reverse, str_one]
    show layP _ [] (bitsOf []) = _
    unfold layP
    simp [bitsOf]
  refine ⟨_, c2, h1.trans (h2.trans hR), ?_, hc2, e1 ▸ hr2⟩
  rw [hdR_eqP]
  show (130 : Nat) = 130
  rfl

theorem pairStepPoly (st : PSt) (hK : 1 ≤ st.K) (hA : 1 ≤ st.A) (hv : st.v < 2 ^ st.n) :
    ∃ N, 0 < N ∧ zppolyLogic.Seg (layPoly st) N (layPoly (polyStep st)) (polyOver st) := by
  by_cases ho : polyOver st
  · obtain ⟨c1, c2, h1, hq, hs, h2⟩ := reachOver st hK hA ho
    obtain ⟨a, ha⟩ := h1
    obtain ⟨n2, hn2⟩ := h2
    refine ⟨a + 1 + n2, by omega, fun h => absurd ho h, fun _ => ⟨a, c1, c2, by omega, ha, hq, hs, ?_⟩⟩
    have : a + 1 + n2 - a - 1 = n2 := by omega
    rw [this]; exact hn2
  · have hm : ∃ m : ZC, m.q ≠ Q.GRB ∧ zppolyLogic.Reach (layPoly st) m ∧
        zppolyLogic.Reach m (layPoly (polyStep st)) := by
      by_cases hok : okv st.K st.n st.A st.v
      · exact reachOk st hK hA hv ho hok
      · exact reachWrong st hK hA hv ho hok
    obtain ⟨m, hq, h1, h2⟩ := hm
    have hq' : (layPoly st).q ≠ m.q := by
      unfold layPoly; rw [layP_q]; exact fun h => hq h.symm
    obtain ⟨n, hn, hr⟩ := LTM.Reach.seg_pos h1 hq' h2
    exact ⟨n, hn, fun _ => hr, fun h => absurd h ho⟩

end ZP.Poly
