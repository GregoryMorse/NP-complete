module

public import ZP.Gx
public import ZP.Decide

@[expose] public section

/-!
# Polynomial bounds for the reduction

* `dx_bound`: with `Q = (n+2)^(k+m+qm V+30)`, the run of `DX V k m x` on an honest
  certificate takes fewer than `Q^5` steps, and the certificate layout is shorter.
* `gen_le`: the generator runs within `Q^3` steps, `Q = (n+2)^(E+F0+30)`.
* `dec_bound`: generator followed by `PD` meets the clock of `rm_ok`.
-/

namespace ZP.Cx

theorem mulX {a b c1 c2 X : Nat} (ha : a ≤ c1 * X) (hb : b ≤ c2 * X) :
    a * b ≤ (c1 * c2) * (X * X) := by
  calc a * b ≤ (c1 * X) * (c2 * X) := Nat.mul_le_mul ha hb
    _ = (c1 * c2) * (X * X) := by ac_rfl

theorem mulQ {a b c Q : Nat} (ha : a ≤ Q) (hb : b ≤ c * Q) : a * b ≤ c * (Q * Q) := by
  calc a * b ≤ Q * (c * Q) := Nat.mul_le_mul ha hb
    _ = c * (Q * Q) := by ac_rfl

theorem pow3 (Y : Nat) : Y ^ 3 = Y * Y * Y := by
  show Y ^ (0 + 1 + 1 + 1) = _
  rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]

theorem pow4 (Y : Nat) : Y ^ 4 = Y * Y * Y * Y := by
  show Y ^ (0 + 1 + 1 + 1 + 1) = _
  rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]

theorem pow5 (Y : Nat) : Y ^ 5 = (Y * Y) * (Y * Y) * Y := by
  show Y ^ (0 + 1 + 1 + 1 + 1 + 1) = _
  rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_zero,
    Nat.one_mul]
  ac_rfl

/-- Facts about `Q = (n+2)^R` used below. -/
theorem big_pow (n R : Nat) (hR : 30 ≤ R) :
    1073741824 ≤ (n + 2) ^ R ∧ n + 2 ≤ (n + 2) ^ R ∧ ∀ c, c ≤ R → c ≤ (n + 2) ^ R := by
  have h2 : 2 ^ R ≤ (n + 2) ^ R := Nat.pow_le_pow_left (by omega) R
  refine ⟨Nat.le_trans (show 2 ^ 30 ≤ 2 ^ R from Nat.pow_le_pow_right (by decide) hR) h2, ?_,
    fun c hc => ?_⟩
  · have := Nat.pow_le_pow_right (show 1 ≤ n + 2 by omega) (show 1 ≤ R by omega)
    simpa using this
  · exact Nat.le_trans (Nat.le_of_lt (lt_2pow c))
      (Nat.le_trans (Nat.pow_le_pow_right (by decide) hc) h2)

theorem dx_bound (V : Mach) (k m n c t Q : Nat) (hQ : 1073741824 ≤ Q) (hn : n + 2 ≤ Q) (hk : k ≤ Q)
    (hm : m ≤ Q) (hq : qm V ≤ Q) (hT : (n + 2) ^ k ≤ Q) (hc : c ≤ (n + 2) ^ k * m)
    (ht : t ≤ bodyB V k m n c) :
    dxT n c t < Q ^ 5 ∧ 2 * n + 2 * c + 4 ≤ Q ^ 5 := by
  have hQQ : Q * 1073741824 ≤ Q * Q := Nat.mul_le_mul_left Q hQ
  have f1 : (n + 2) ^ k * m ≤ 1 * (Q * Q) := by rw [Nat.one_mul]; exact Nat.mul_le_mul hT hm
  have f2 : (n + 2) ^ k * (8 * m + 4) ≤ 9 * (Q * Q) := mulQ hT (by omega)
  have f3 : (n + 2) ^ k * (sB V ((n + 2) ^ k) + 2) ≤ 6 * (Q * Q) :=
    mulQ hT (by unfold sB; omega)
  have f4 : powB (n + 2) k ≤ 17 * (Q * Q) + 1 := by
    have h1 := powB_le (n + 2) (by omega) k
    have h2 : k * (16 * (n + 2) ^ k + 2) ≤ 17 * (Q * Q) := mulQ hk (by omega)
    omega
  rw [pow5]
  obtain ⟨QQ, hQQd⟩ : ∃ QQ, QQ = Q * Q := ⟨_, rfl⟩
  rw [← hQQd] at hQQ f1 f2 f3 f4 ⊢
  have hb : t ≤ 90 * QQ := by
    unfold bodyB preB mainB at ht
    generalize (n + 2) ^ k * m = A1 at f1 ht hc
    generalize (n + 2) ^ k * (8 * m + 4) = A2 at f2 ht
    generalize (n + 2) ^ k * (sB V ((n + 2) ^ k) + 2) = A3 at f3 ht
    generalize powB (n + 2) k = A4 at f4 ht
    generalize (n + 2) ^ k = T at hT ht
    omega
  have hcQ : c ≤ QQ := by omega
  have hs : 2 * n + 2 * c + 2 * t + 26 ≤ 183 * QQ := by omega
  have hp : t * (2 * n + 2 * c + 2 * t + 26) ≤ (90 * 183) * (QQ * QQ) := mulX hb hs
  have hQ4 : QQ * 1073741824 ≤ QQ * QQ := Nat.mul_le_mul_left QQ (by omega)
  have hQ5 : QQ * QQ * 1073741824 ≤ QQ * QQ * Q := Nat.mul_le_mul_left _ hQ
  unfold dxT
  rw [Nat.mul_assoc 40 t]
  generalize t * (2 * n + 2 * c + 2 * t + 26) = P at hp ⊢
  generalize QQ * QQ = Q4 at hp hQ4 hQ5 ⊢
  generalize Q4 * Q = Q5 at hQ5 ⊢
  omega

theorem gen_le (V : Mach) (k m E n Q : Nat) (hQ : 1073741824 ≤ Q) (hn : n + 2 ≤ Q)
    (hp : (n + 2) ^ E ≤ Q) (hF : F0 V k m ≤ Q) (hE : E ≤ Q) : genB V k m E n ≤ Q * Q * Q := by
  have hQQ : Q * 1073741824 ≤ Q * Q := Nat.mul_le_mul_left Q hQ
  have f1 : F0 V k m * (27 * (3 * F0 V k m + 6 * n + 11 + (n + 2) ^ E) + 21) ≤ 300 * (Q * Q) :=
    mulQ hF (by omega)
  have f2 : n * (54 * (3 * F0 V k m + 6 * n + 11 + (n + 2) ^ E) + 43) ≤ 600 * (Q * Q) :=
    mulQ (by omega) (by omega)
  have f3 : powB (n + 2) E ≤ 18 * (Q * Q) + 1 := by
    have h1 := powB_le (n + 2) (by omega) E
    have h2 : E * (16 * (n + 2) ^ E + 2) ≤ 18 * (Q * Q) := mulQ hE (by omega)
    omega
  have hQ3 : Q * Q * 1073741824 ≤ Q * Q * Q := Nat.mul_le_mul_left _ hQ
  unfold genB genT
  generalize F0 V k m * (27 * (3 * F0 V k m + 6 * n + 11 + (n + 2) ^ E) + 21) = A1 at f1 ⊢
  generalize n * (54 * (3 * F0 V k m + 6 * n + 11 + (n + 2) ^ E) + 43) = A2 at f2 ⊢
  generalize powB (n + 2) E = A3 at f3 ⊢
  generalize Q * Q * Q = Q3 at hQ3 ⊢
  generalize Q * Q = QQ at hQQ f1 f2 f3 hQ3
  generalize (n + 2) ^ E = pd at hp ⊢
  generalize F0 V k m = F at hF ⊢
  omega

/-- The final clock: `Y = Q^(4e)` bounds both phases. -/
theorem fin_bound (n t Y : Nat) (hY : 1073741824 ≤ Y) (hn : n ≤ Y) (ht : t ≤ 2 * Y) :
    40 * n + n * (16 * n + 28) + 16 * 6 + 100 + 40 * t * (2 * n + 2 * 6 + 2 * t + 8) < Y ^ 3 := by
  have f1 : n * (16 * n + 28) ≤ 17 * (Y * Y) := mulQ hn (by omega)
  have f2 : t * (2 * n + 2 * 6 + 2 * t + 8) ≤ (2 * 7) * (Y * Y) := mulX ht (by omega)
  have hYY : Y * 1073741824 ≤ Y * Y := Nat.mul_le_mul_left Y hY
  have hY3 : Y * Y * 1073741824 ≤ Y * Y * Y := Nat.mul_le_mul_left _ hY
  rw [pow3, Nat.mul_assoc 40 t]
  generalize n * (16 * n + 28) = A1 at f1 ⊢
  generalize t * (2 * n + 2 * 6 + 2 * t + 8) = A2 at f2 ⊢
  generalize Y * Y * Y = Y3 at hY3 ⊢
  generalize Y * Y = YY at f1 f2 hYY hY3
  omega

theorem dec_bound (V : Mach) (k m E : Nat) (G : Mach) (K n s tg tp : Nat) (hs : s ≤ n + tg)
    (htg : tg ≤ genB V k m E n) (htp : tp ≤ pdB G K s) :
    40 * n + n * (16 * n + 28) + 16 * 6 + 100 +
        40 * (tg + tp) * (2 * n + 2 * 6 + 2 * (tg + tp) + 8) <
      (n + 2) ^ ((E + F0 V k m + 30) * (12 * (18 * (K + qm G + 8) + 1))) := by
  obtain ⟨e, he⟩ : ∃ e, e = 18 * (K + qm G + 8) + 1 := ⟨_, rfl⟩
  rw [← he]
  obtain ⟨hQ, hn2, hc⟩ := big_pow n (E + F0 V k m + 30) (by omega)
  generalize hQd : (n + 2) ^ (E + F0 V k m + 30) = Q at hQ hn2 hc
  have hpad : (n + 2) ^ E ≤ Q := by
    rw [← hQd]; exact Nat.pow_le_pow_right (by omega) (by omega)
  have hg := gen_le V k m E n Q hQ hn2 hpad (hc _ (by omega)) (hc _ (by omega))
  -- the PD phase
  have hpd := pd_lt G K s tp htp
  rw [← he] at hpd
  have htp' : tp < (s + 2) ^ e := by
    have h1 : 1 ≤ 2 * s + 2 * 6 + 2 * tp + 8 := by omega
    have h2 : tp ≤ 40 * tp * (2 * s + 2 * 6 + 2 * tp + 8) := by
      rw [Nat.mul_assoc]
      exact Nat.le_trans (Nat.le_mul_of_pos_right tp h1) (Nat.le_mul_of_pos_left _ (by decide))
    omega
  have hQ1 : 1 ≤ Q := by omega
  have hQQ : Q * 1073741824 ≤ Q * Q := Nat.mul_le_mul_left Q hQ
  have hQ3 : Q * Q * 1073741824 ≤ Q * Q * Q := Nat.mul_le_mul_left _ hQ
  have hQ4 : Q * Q * Q * 1073741824 ≤ Q * Q * Q * Q := Nat.mul_le_mul_left _ hQ
  have hs2 : s + 2 ≤ Q ^ 4 := by
    rw [pow4]
    generalize Q * Q * Q * Q = Q4 at hQ4 ⊢
    generalize Q * Q * Q = Q3 at hg hQ3 hQ4
    generalize Q * Q = QQ at hQQ hQ3
    omega
  have hY : (s + 2) ^ e ≤ Q ^ (4 * e) := by
    rw [Nat.pow_mul]; exact Nat.pow_le_pow_left hs2 e
  have he1 : 1 ≤ e := by omega
  have hQe : Q ^ 4 ≤ Q ^ (4 * e) := Nat.pow_le_pow_right hQ1 (by omega)
  have hQ4' : Q * Q * Q ≤ Q ^ 4 := by rw [pow4]; exact Nat.le_mul_of_pos_right _ hQ1
  have hQY : Q ≤ Q ^ (4 * e) := by
    have := Nat.pow_le_pow_right hQ1 (show 1 ≤ 4 * e by omega)
    simpa using this
  have hYb : 1073741824 ≤ Q ^ (4 * e) := Nat.le_trans hQ hQY
  have hfin := fin_bound n (tg + tp) (Q ^ (4 * e)) hYb (by omega) (by omega)
  rw [← Nat.pow_mul, show 4 * e * 3 = 12 * e by omega] at hfin
  rw [Nat.pow_mul, hQd]
  exact hfin

end ZP.Cx
