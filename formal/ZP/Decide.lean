module

public import ZP.Clock
public import ZP.Raw

@[expose] public section

/-!
# `Sentence → L ∈ P`

`sentence_iff` gives a guest code `J` that decides `L` within `clock J`. The machine
`rm 6 (PD G k)`, with `G = gMach (startCode J)` and `k = |J| + 1`, lays out the input,
builds the clock `(|x| + 2) ^ k - 1` in unary, runs `SIM G` for that many steps and
answers. Its running time is below `(|x| + 2) ^ (18 * (k + qm G + 8) + 1)`.
-/

namespace ZP.Cx

theorem rep_tail {b : Bool} : ∀ n, (List.replicate n b).tail = List.replicate (n - 1) b
  | 0 => rfl
  | n + 1 => by simp

def PD (M : Mach) (k : Nat) : Cmd :=
  .seq (CLK k) (.seq (.pop 3) (.seq (SIM M) (.seq (clr 0) (mv 4 0))))

def pdB (M : Mach) (k n : Nat) : Nat :=
  10 * n + 2 + (3 + powB (n + 2) k) + (1 + (((n + 2) ^ k - 1) * (sB M ((n + 2) ^ k - 1) + 2) + 1 +
    (2 * (n + (n + 2) ^ k) + 1 + 5)))

theorem pd_ok (M : Mach) (k : Nat) (x : List Bool) :
    ∃ S', ExecB (PD M k) (WS x [] [] [] [] [] [] []) S' (pdB M k x.length) ∧
      (S'.getD 0 [] ≠ [] ↔ (zexec M ((x.length + 2) ^ k - 1) 0 [] x).getD false = true) := by
  have e2 := clk_ok (L := []) x k
  have e2' : ExecB (.pop 3)
      (WS x [] [] (List.replicate ((x.length + 2) ^ k) true) [] (List.replicate (x.length + 2) true) [] [])
      (WS x [] [] (List.replicate ((x.length + 2) ^ k - 1) true) [] (List.replicate (x.length + 2) true)
        [] []) 1 :=
    ExecB.pop.to (by
      show [x, [], [], (List.replicate ((x.length + 2) ^ k) true).tail, [],
        List.replicate (x.length + 2) true, [], []] = _
      rw [rep_tail]
      rfl) (Nat.le_refl _)
  obtain ⟨R', L', Q', hl, e3⟩ := sim_ok M [List.replicate (x.length + 2) true, [], []]
    ((x.length + 2) ^ k - 1) 0 [] x (Nat.zero_le _)
  have e3' : ExecB (SIM M)
      (WS x [] [] (List.replicate ((x.length + 2) ^ k - 1) true) [] (List.replicate (x.length + 2) true)
        [] [])
      (WS R' L' Q' [] (ansOf ((zexec M ((x.length + 2) ^ k - 1) 0 [] x).getD false))
        (List.replicate (x.length + 2) true) [] [])
      (((x.length + 2) ^ k - 1) * (sB M ((x.length + 2) ^ k - 1) + 2) + 1) := e3
  generalize (zexec M ((x.length + 2) ^ k - 1) 0 [] x).getD false = b at e3' ⊢
  have e4 : ExecB (clr 0) (WS R' L' Q' [] (ansOf b) (List.replicate (x.length + 2) true) [] [])
      (WS [] L' Q' [] (ansOf b) (List.replicate (x.length + 2) true) [] []) (2 * R'.length + 1) :=
    (clr_ok (i := 0) R' _ (by simp [WS]) rfl).to rfl (Nat.le_refl _)
  have e5 := mv_ok (i := 4) (j := 0) (by decide) (ansOf b)
    (WS [] L' Q' [] (ansOf b) (List.replicate (x.length + 2) true) [] []) (by simp [WS])
    (by simp [WS]) rfl
  refine ⟨_, (e2.seq (e2'.seq (e3'.seq (e4.seq e5)))).to rfl ?_, ?_⟩
  · have := length_ansOf b
    simp only [List.length_nil, Nat.add_zero] at hl
    unfold pdB
    generalize ((x.length + 2) ^ k - 1) * (sB M ((x.length + 2) ^ k - 1) + 2) = K
    generalize (x.length + 2) ^ k = T at hl ⊢
    generalize powB (x.length + 2) k = B
    omega
  · cases b <;> simp [WS, ansOf]

theorem ok_PD (M : Mach) (k : Nat) : Ok 8 (PD M k) :=
  ⟨⟨okb_ok 8 LEN (by decide), okb_ok 8 _ (by decide), ok_POW k⟩, okb_ok 8 (.pop 3) (by decide),
    ok_SIM (by decide) M, okb_ok 8 (clr 0) (by decide), okb_ok 8 (mv 4 0) (by decide)⟩

/-! ## The time bound -/

theorem w_aux (n t P : Nat) (h : 2 * n + 20 + 2 * t ≤ P) : 2 * n + 2 * 6 + 2 * t + 8 ≤ P := by
  omega

theorem li_aux (n X P : Nat) (h : 40 * n + 196 + X ≤ P) : 40 * n + X + 16 * 6 + 100 ≤ P := by
  omega

theorem ht_aux (n t K1 K2 P7 P T : Nat) (ht : t ≤ 12 * n + 13 + P + K2 + 2 * T)
    (hP : P ≤ K1 + 1) (c5 : K1 + 1 + K2 + (12 * n + 13 + 2 * T) ≤ P7) : t ≤ P7 := by
  omega

theorem rd_bound (n k Z T Q P S t : Nat) (hQ : 128 * (n + 2) ≤ Q) (hT : T ≤ Q) (hZ : Z ≤ Q)
    (hk : k ≤ Q) (hP : P ≤ k * (16 * T + 2) + 1) (hS : S ≤ 2 * T + 3 * Z + 10)
    (ht : t ≤ 12 * n + 13 + P + T * (S + 2) + 2 * T) :
    40 * n + n * (16 * n + 28) + 16 * 6 + 100 + 40 * t * (2 * n + 2 * 6 + 2 * t + 8) ≤
      pw Q 18 := by
  have hQ2 : 2 ≤ Q := by omega
  have hQ1 : 1 ≤ Q := by omega
  have a1 : 16 * T ≤ pw Q 2 := qmul (q1 (show 16 ≤ Q by omega)) (q1 hT) rfl
  have a2 : 2 ≤ pw Q 2 := qup hQ1 (q1 hQ2) (by decide)
  have a3 : 16 * T + 2 ≤ pw Q 3 := qadd hQ2 a1 a2 rfl
  have a4 : k * (16 * T + 2) ≤ pw Q 4 := qmul (q1 hk) a3 rfl
  have a5 : 1 ≤ pw Q 4 := qup hQ1 (q1 hQ1) (by decide)
  have a6 : k * (16 * T + 2) + 1 ≤ pw Q 5 := qadd hQ2 a4 a5 rfl
  have b1 : 2 * T ≤ pw Q 2 := qmul (q1 hQ2) (q1 hT) rfl
  have b2 : 3 * Z ≤ pw Q 2 := qmul (q1 (show 3 ≤ Q by omega)) (q1 hZ) rfl
  have b3 : 2 * T + 3 * Z ≤ pw Q 3 := qadd hQ2 b1 b2 rfl
  have b4 : 12 ≤ pw Q 3 := qup hQ1 (q1 (show 12 ≤ Q by omega)) (by decide)
  have b5 : 2 * T + 3 * Z + 12 ≤ pw Q 4 := qadd hQ2 b3 b4 rfl
  have b5' : S + 2 ≤ pw Q 4 := by
    generalize pw Q 4 = P4 at b5 ⊢
    omega
  have b6 : T * (S + 2) ≤ pw Q 5 := qmul (q1 hT) b5' rfl
  have c1 : 12 * n + 13 ≤ pw Q 2 := qup hQ1 (q1 (by omega)) (by decide)
  have c2 : 12 * n + 13 + 2 * T ≤ pw Q 3 := qadd hQ2 c1 b1 rfl
  have c3 : k * (16 * T + 2) + 1 + T * (S + 2) ≤ pw Q 6 := qadd hQ2 a6 b6 rfl
  have c4 : 12 * n + 13 + 2 * T ≤ pw Q 6 := qup hQ1 c2 (by decide)
  have c5 : k * (16 * T + 2) + 1 + T * (S + 2) + (12 * n + 13 + 2 * T) ≤ pw Q 7 :=
    qadd hQ2 c3 c4 rfl
  have ht' : t ≤ pw Q 7 := ht_aux n t _ _ _ _ _ ht hP c5
  have w1 : 2 * n + 20 ≤ pw Q 7 := qup hQ1 (q1 (by omega)) (by decide)
  have w2 : 2 * t ≤ pw Q 8 := qmul (q1 hQ2) ht' rfl
  have w3 : 2 * n + 20 + 2 * t ≤ pw Q 9 := qadd hQ2 (qup hQ1 w1 (by decide)) w2 rfl
  have w : 2 * n + 2 * 6 + 2 * t + 8 ≤ pw Q 9 := w_aux n t _ w3
  have v : 40 * t ≤ pw Q 8 := qmul (q1 (show 40 ≤ Q by omega)) ht' rfl
  have pr : 40 * t * (2 * n + 2 * 6 + 2 * t + 8) ≤ pw Q 17 := qmul v w rfl
  have x3 : n * (16 * n + 28) ≤ pw Q 2 :=
    qmul (q1 (show n ≤ Q by omega)) (q1 (show 16 * n + 28 ≤ Q by omega)) rfl
  have y : 40 * n + 196 + n * (16 * n + 28) ≤ pw Q 3 :=
    qadd hQ2 (qup hQ1 (q1 (show 40 * n + 196 ≤ Q by omega)) (by decide)) x3 rfl
  have li : 40 * n + n * (16 * n + 28) + 16 * 6 + 100 ≤ pw Q 17 :=
    li_aux n _ _ (qup hQ1 y (by decide))
  exact qadd hQ2 li pr rfl

theorem pd_lt (M : Mach) (k n t : Nat) (ht : t ≤ pdB M k n) :
    40 * n + n * (16 * n + 28) + 16 * 6 + 100 + 40 * t * (2 * n + 2 * 6 + 2 * t + 8) <
      (n + 2) ^ (18 * (k + qm M + 8) + 1) := by
  have hN : 1 ≤ n + 2 := by omega
  have hP := powB_le (n + 2) hN k
  have hQ : 128 * (n + 2) ≤ (n + 2) ^ (k + qm M + 8) :=
    Nat.le_trans (lin8 n) (Nat.pow_le_pow_right hN (by omega))
  have hT : (n + 2) ^ k ≤ (n + 2) ^ (k + qm M + 8) := Nat.pow_le_pow_right hN (by omega)
  have hZ : qm M ≤ (n + 2) ^ (k + qm M + 8) :=
    Nat.le_trans (Nat.le_of_lt (lt_2pow _))
      (Nat.le_trans (Nat.pow_le_pow_left (show 2 ≤ n + 2 by omega) _)
        (Nat.pow_le_pow_right hN (by omega)))
  have hk : k ≤ (n + 2) ^ (k + qm M + 8) :=
    Nat.le_trans (Nat.le_of_lt (lt_2pow _))
      (Nat.le_trans (Nat.pow_le_pow_left (show 2 ≤ n + 2 by omega) _)
        (Nat.pow_le_pow_right hN (by omega)))
  have hS : sB M ((n + 2) ^ k) ≤ 2 * (n + 2) ^ k + 3 * qm M + 10 := by unfold sB; exact Nat.le_refl _
  have hmono : ((n + 2) ^ k - 1) * (sB M ((n + 2) ^ k - 1) + 2) ≤
      (n + 2) ^ k * (sB M ((n + 2) ^ k) + 2) :=
    Nat.mul_le_mul (Nat.sub_le _ _) (by unfold sB; omega)
  have ht' : t ≤ 12 * n + 13 + powB (n + 2) k + (n + 2) ^ k * (sB M ((n + 2) ^ k) + 2) +
      2 * (n + 2) ^ k := by
    unfold pdB at ht
    generalize ((n + 2) ^ k - 1) * (sB M ((n + 2) ^ k - 1) + 2) = K' at ht hmono
    generalize (n + 2) ^ k * (sB M ((n + 2) ^ k) + 2) = K at ht hmono ⊢
    generalize (n + 2) ^ k = T at ht ⊢
    generalize powB (n + 2) k = B at ht ⊢
    clear hP hQ hT hZ hk hS
    omega
  have h := rd_bound n k (qm M) ((n + 2) ^ k) _ (powB (n + 2) k) (sB M ((n + 2) ^ k)) t
    hQ hT hZ hk hP hS ht'
  rw [pw_eq, ← Nat.pow_mul] at h
  refine Nat.lt_of_le_of_lt h (Nat.pow_lt_pow_right (Nat.lt_of_lt_of_le (by decide)
    (Nat.le_add_left 2 n)) ?_)
  clear h hP hQ hT hZ hk hS ht' ht hmono
  generalize qm M = Z
  omega

/-! ## The decider -/

theorem InP_of_Sentence (h : Sentence) : InP Lp := by
  obtain ⟨J, hJ⟩ := sentence_iff.mp h
  refine ⟨rm 6 (PD (gMach (startCode J)) (J.length + 1)),
    18 * (J.length + 1 + qm (gMach (startCode J)) + 8) + 1, fun x => ?_⟩
  obtain ⟨S', ⟨t, ht, hE⟩, hiff⟩ := pd_ok (gMach (startCode J)) (J.length + 1) x
  have hE' : Exec (PD (gMach (startCode J)) (J.length + 1)) (x :: List.replicate (6 + 1) []) S' t :=
    hE
  refine ⟨_, rm_ok 6 (ok_PD _ _) hE' _ (pd_lt _ _ x.length t ht), ?_⟩
  have hr := hJ x
  rw [run_eq] at hr
  unfold clock at hr
  have hz : zexec (gMach (startCode J)) ((x.length + 2) ^ (J.length + 1) - 1) 0 [] x =
      exec (gMach (startCode J)) ((x.length + 2) ^ (J.length + 1) - 1) 0 (inTape x) 0 :=
    (exec_z _ _ 0 [] x).symm.trans (by rw [inTape_z])
  unfold Lp
  rw [← hr, ← hz, ← hiff]
  exact decide_eq_true_iff

end ZP.Cx
