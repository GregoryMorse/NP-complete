module

public import ZP.Sim
public import ZP.Verif

@[expose] public section

/-!
# Unary clocks, and `P ⊆ NP`

On eight stacks `[R, L, Q, C, A, N, D, T]` (`SIM`'s five, then three scratch stacks):

* `LEN` puts `|R|` ones on `N` and keeps `R`;
* `MUL` replaces `C` (`c` ones) by `c · a` ones, where `N` holds `a` ones;
* `POWk k` turns `C = [1]` into `a ^ k` ones.

`PV M k` clears the certificate, builds the clock `(|x| + 2) ^ k`, runs `SIM M` on the
input, and leaves the answer on stack 0. Run by the verifier `vm` of `ZP/Verif.lean`,
it decides membership with the certificate `[]`: `InP_InNP`.
-/

namespace ZP.Cx

def WS (R L Q C A N D T : List Bool) : List (List Bool) := [R, L, Q, C, A, N, D, T]

/-! ## Length -/

def lb (b : Bool) : Cmd := .seq (.pop 0) (.seq (.push 7 b) (.push 5 true))
def LEN1 : Cmd := .wh 0 false true true (.cs 0 .skip (lb false) (lb true))
def LEN : Cmd := .seq LEN1 (mv 7 0)

theorem len1_ok {L Q C A D : List Bool} : ∀ (u N T : List Bool),
    ExecB LEN1 (WS u L Q C A N D T)
      (WS [] L Q C A (List.replicate u.length true ++ N) D (u.reverse ++ T)) (6 * u.length + 1)
  | [], N, T => ExecB.to (ExecB.whF (by rfl)) rfl (by omega)
  | b :: u, N, T => by
    have hb : ExecB (lb b) (WS (b :: u) L Q C A N D T) (WS u L Q C A (true :: N) D (b :: T)) 3 :=
      (ExecB.pop.seq (ExecB.push.seq ExecB.push)).to rfl (Nat.le_refl _)
    have hb' : ExecB (sel (b :: u) .skip (lb false) (lb true)) (WS (b :: u) L Q C A N D T)
        (WS u L Q C A (true :: N) D (b :: T)) 3 := by
      cases b <;> exact hb
    have ih := len1_ok (L := L) (Q := Q) (C := C) (A := A) (D := D) u (true :: N) (b :: T)
    refine (ExecB.whT (by cases b <;> rfl) (ExecB.cs (by exact hb')) ih).to ?_
      (by simp only [List.length_cons]; omega)
    simp [WS, List.replicate_succ']

theorem len_ok {L Q C A D N : List Bool} (u : List Bool) :
    ExecB LEN (WS u L Q C A N D []) (WS u L Q C A (List.replicate u.length true ++ N) D [])
      (10 * u.length + 2) := by
  have h1 := len1_ok (L := L) (Q := Q) (C := C) (A := A) (D := D) u N []
  have h2 := mv_ok (i := 7) (j := 0) (by decide) (u.reverse ++ [])
    (WS [] L Q C A (List.replicate u.length true ++ N) D (u.reverse ++ [])) (by simp [WS])
    (by simp [WS]) rfl
  have h2' : ExecB (mv 7 0) (WS [] L Q C A (List.replicate u.length true ++ N) D (u.reverse ++ []))
      (WS u L Q C A (List.replicate u.length true ++ N) D []) (4 * u.length + 1) :=
    h2.to (by simp [WS]) (by simp)
  exact (h1.seq h2').to rfl (by omega)

/-! ## Addition and multiplication -/

def ab : Cmd := .seq (.pop 5) (.seq (.push 7 true) (.push 6 true))
def ADD1 : Cmd := .wh 5 false true true ab
def ADDN : Cmd := .seq ADD1 (mv 7 5)

theorem add1_ok {R L Q C A : List Bool} : ∀ (a : Nat) (D T : List Bool),
    ExecB ADD1 (WS R L Q C A (List.replicate a true) D T)
      (WS R L Q C A [] (List.replicate a true ++ D) (List.replicate a true ++ T)) (4 * a + 1)
  | 0, D, T => ExecB.to (ExecB.whF (by rfl)) rfl (by omega)
  | a + 1, D, T => by
    have hb : ExecB ab (WS R L Q C A (List.replicate (a + 1) true) D T)
        (WS R L Q C A (List.replicate a true) (true :: D) (true :: T)) 3 :=
      (ExecB.pop.seq (ExecB.push.seq ExecB.push)).to rfl (Nat.le_refl _)
    have ih := add1_ok (R := R) (L := L) (Q := Q) (C := C) (A := A) a (true :: D) (true :: T)
    refine (ExecB.whT (by rfl) hb ih).to ?_ (by omega)
    simp [WS, List.replicate_succ']

theorem addn_ok {R L Q C A : List Bool} (a : Nat) (D : List Bool) :
    ExecB ADDN (WS R L Q C A (List.replicate a true) D [])
      (WS R L Q C A (List.replicate a true) (List.replicate a true ++ D) []) (8 * a + 2) := by
  have h1 := add1_ok (R := R) (L := L) (Q := Q) (C := C) (A := A) a D []
  have h2 := mv_ok (i := 7) (j := 5) (by decide) (List.replicate a true ++ [])
    (WS R L Q C A [] (List.replicate a true ++ D) (List.replicate a true ++ [])) (by simp [WS])
    (by simp [WS]) rfl
  have h2' : ExecB (mv 7 5) (WS R L Q C A [] (List.replicate a true ++ D) (List.replicate a true ++ []))
      (WS R L Q C A (List.replicate a true) (List.replicate a true ++ D) []) (4 * a + 1) :=
    h2.to (by simp [WS]) (by simp)
  exact (h1.seq h2').to rfl (by omega)

theorem rep_add (b : Bool) : ∀ n m : Nat,
    List.replicate (n + m) b = List.replicate n b ++ List.replicate m b
  | 0, _ => by simp
  | n + 1, m => by
    rw [Nat.succ_add, List.replicate_succ, List.replicate_succ, rep_add b n m]; rfl

def mb : Cmd := .seq (.pop 3) ADDN
def MUL1 : Cmd := .wh 3 false true true mb
def MUL : Cmd := .seq MUL1 (mv 6 3)

theorem mul1_ok {R L Q A : List Bool} (a : Nat) : ∀ (c : Nat) (D : List Bool),
    ExecB MUL1 (WS R L Q (List.replicate c true) A (List.replicate a true) D [])
      (WS R L Q [] A (List.replicate a true) (List.replicate (c * a) true ++ D) [])
      (c * (8 * a + 4) + 1)
  | 0, D => ExecB.to (ExecB.whF (by rfl)) (by simp) (by omega)
  | c + 1, D => by
    have hp : ExecB (.pop 3) (WS R L Q (List.replicate (c + 1) true) A (List.replicate a true) D [])
        (WS R L Q (List.replicate c true) A (List.replicate a true) D []) 1 :=
      ExecB.pop.to rfl (Nat.le_refl _)
    have hd := addn_ok (R := R) (L := L) (Q := Q) (C := List.replicate c true) (A := A) a D
    have ih := mul1_ok (R := R) (L := L) (Q := Q) (A := A) a c (List.replicate a true ++ D)
    refine (ExecB.whT (by rfl) (hp.seq hd) ih).to ?_ ?_
    · rw [Nat.add_mul, Nat.one_mul, rep_add true (c * a) a, List.append_assoc]
    · have := Nat.add_mul c 1 (8 * a + 4)
      omega

theorem mul_ok {R L Q A : List Bool} (a c : Nat) :
    ExecB MUL (WS R L Q (List.replicate c true) A (List.replicate a true) [] [])
      (WS R L Q (List.replicate (c * a) true) A (List.replicate a true) [] [])
      (c * (8 * a + 4) + 4 * (c * a) + 2) := by
  have h1 := mul1_ok (R := R) (L := L) (Q := Q) (A := A) a c []
  have h2 := mv_ok (i := 6) (j := 3) (by decide) (List.replicate (c * a) true ++ [])
    (WS R L Q [] A (List.replicate a true) (List.replicate (c * a) true ++ []) []) (by simp [WS])
    (by simp [WS]) rfl
  have h2' : ExecB (mv 6 3) (WS R L Q [] A (List.replicate a true) (List.replicate (c * a) true ++ []) [])
      (WS R L Q (List.replicate (c * a) true) A (List.replicate a true) [] []) (4 * (c * a) + 1) :=
    h2.to (by simp [WS]) (by simp)
  exact (h1.seq h2').to rfl (by omega)

def POWk : Nat → Cmd
  | 0 => .skip
  | k + 1 => .seq (POWk k) MUL

def powB (a : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => powB a k + (a ^ k * (8 * a + 4) + 4 * (a ^ k * a) + 2)

theorem pow_ok {R L Q A : List Bool} (a : Nat) : ∀ k : Nat,
    ExecB (POWk k) (WS R L Q [true] A (List.replicate a true) [] [])
      (WS R L Q (List.replicate (a ^ k) true) A (List.replicate a true) [] []) (powB a k)
  | 0 => ExecB.skip.to rfl (Nat.le_refl _)
  | k + 1 => by
    have ih := pow_ok (R := R) (L := L) (Q := Q) (A := A) a k
    have hm := mul_ok (R := R) (L := L) (Q := Q) (A := A) a (a ^ k)
    exact (ih.seq hm).to rfl (Nat.le_refl _)

theorem powB_le (a : Nat) (ha : 1 ≤ a) : ∀ k, powB a k ≤ k * (16 * a ^ k + 2) + 1
  | 0 => by simp [powB]
  | k + 1 => by
    have ih := powB_le a ha k
    have hP : a ^ k ≤ a ^ (k + 1) := Nat.pow_le_pow_right ha (by omega)
    have e1 : a ^ (k + 1) = a ^ k * a := by rw [Nat.pow_succ]
    have e2 : a ^ k * (8 * a + 4) = 8 * (a ^ k * a) + 4 * a ^ k := by
      rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm (a ^ k) 4]
    have h3 := Nat.mul_le_mul_left k (show 16 * a ^ k + 2 ≤ 16 * a ^ (k + 1) + 2 by omega)
    have h4 : (k + 1) * (16 * a ^ (k + 1) + 2) = k * (16 * a ^ (k + 1) + 2) + (16 * a ^ (k + 1) + 2) := by
      rw [Nat.add_mul, Nat.one_mul]
    simp only [powB]
    rw [e2]
    rw [e1] at h3 h4 hP ⊢
    generalize a ^ k * a = P1 at h3 h4 hP ⊢
    generalize a ^ k = P at ih h3 hP ⊢
    generalize k * (16 * P + 2) = K1 at ih h3
    generalize k * (16 * P1 + 2) = K2 at h3 h4
    generalize (k + 1) * (16 * P1 + 2) = K3 at h4 ⊢
    generalize powB a k = B at ih ⊢
    omega

/-! ## The verifier program -/

def CLK (k : Nat) : Cmd := .seq LEN (.seq (.seq (.push 5 true) (.seq (.push 5 true) (.push 3 true))) (POWk k))

theorem clk_ok {L : List Bool} (x : List Bool) (k : Nat) :
    ExecB (CLK k) (WS x L [] [] [] [] [] [])
      (WS x L [] (List.replicate ((x.length + 2) ^ k) true) [] (List.replicate (x.length + 2) true) [] [])
      (10 * x.length + 2 + (3 + powB (x.length + 2) k)) := by
  have h1 := len_ok (L := L) (Q := []) (C := []) (A := []) (D := []) (N := []) x
  have h2 : ExecB (.seq (.push 5 true) (.seq (.push 5 true) (.push 3 true)))
      (WS x L [] [] [] (List.replicate x.length true ++ []) [] [])
      (WS x L [] [true] [] (true :: true :: List.replicate x.length true) [] []) 3 :=
    (ExecB.push.seq (ExecB.push.seq ExecB.push)).to (by simp [WS]) (Nat.le_refl _)
  have h3 := pow_ok (R := x) (L := L) (Q := []) (A := []) (x.length + 2) k
  exact (h1.seq (h2.seq h3)).to rfl (Nat.le_refl _)

def PV (M : Mach) (k : Nat) : Cmd :=
  .seq (clr 1) (.seq (CLK k) (.seq (SIM M) (.seq (clr 0) (mv 4 0))))

def pvB (M : Mach) (k n m : Nat) : Nat :=
  2 * m + 1 + (10 * n + 2 + (3 + powB (n + 2) k) +
    ((n + 2) ^ k * (sB M ((n + 2) ^ k) + 2) + 1 + (2 * (n + (n + 2) ^ k) + 1 + 5)))

theorem length_ansOf (b : Bool) : (ansOf b).length ≤ 1 := by cases b <;> simp [ansOf]

theorem pv_ok (M : Mach) (k : Nat) (x y : List Bool) :
    ∃ S', ExecB (PV M k) (WS x y [] [] [] [] [] []) S' (pvB M k x.length y.length) ∧
      (S'.getD 0 [] ≠ [] ↔ (zexec M ((x.length + 2) ^ k) 0 [] x).getD false = true) := by
  have e1 : ExecB (clr 1) (WS x y [] [] [] [] [] []) (WS x [] [] [] [] [] [] []) (2 * y.length + 1) :=
    (clr_ok (i := 1) y _ (by simp [WS]) rfl).to rfl (Nat.le_refl _)
  have e2 := clk_ok (L := []) x k
  obtain ⟨R', L', Q', hl, e3⟩ := sim_ok M [List.replicate (x.length + 2) true, [], []]
    ((x.length + 2) ^ k) 0 [] x (Nat.zero_le _)
  have e3' : ExecB (SIM M)
      (WS x [] [] (List.replicate ((x.length + 2) ^ k) true) [] (List.replicate (x.length + 2) true) [] [])
      (WS R' L' Q' [] (ansOf ((zexec M ((x.length + 2) ^ k) 0 [] x).getD false))
        (List.replicate (x.length + 2) true) [] [])
      ((x.length + 2) ^ k * (sB M ((x.length + 2) ^ k) + 2) + 1) := e3
  generalize (zexec M ((x.length + 2) ^ k) 0 [] x).getD false = b at e3' ⊢
  have e4 : ExecB (clr 0) (WS R' L' Q' [] (ansOf b) (List.replicate (x.length + 2) true) [] [])
      (WS [] L' Q' [] (ansOf b) (List.replicate (x.length + 2) true) [] []) (2 * R'.length + 1) :=
    (clr_ok (i := 0) R' _ (by simp [WS]) rfl).to rfl (Nat.le_refl _)
  have e5 := mv_ok (i := 4) (j := 0) (by decide) (ansOf b)
    (WS [] L' Q' [] (ansOf b) (List.replicate (x.length + 2) true) [] []) (by simp [WS])
    (by simp [WS]) rfl
  refine ⟨_, (e1.seq (e2.seq (e3'.seq (e4.seq e5)))).to rfl ?_, ?_⟩
  · have := length_ansOf b
    simp only [List.length_nil, Nat.add_zero] at hl
    unfold pvB
    generalize (x.length + 2) ^ k * (sB M ((x.length + 2) ^ k) + 2) = K
    generalize (x.length + 2) ^ k = T at hl ⊢
    generalize powB (x.length + 2) k = B
    omega
  · cases b <;> simp [WS, ansOf]

theorem ok_POW : ∀ k, Ok 8 (POWk k)
  | 0 => trivial
  | k + 1 => ⟨ok_POW k, okb_ok 8 MUL (by decide)⟩

theorem ok_PV (M : Mach) (k : Nat) : Ok 8 (PV M k) :=
  ⟨okb_ok 8 (clr 1) (by decide), ⟨okb_ok 8 LEN (by decide), okb_ok 8 _ (by decide), ok_POW k⟩,
    ok_SIM (by decide) M, okb_ok 8 (clr 0) (by decide), okb_ok 8 (mv 4 0) (by decide)⟩

/-! ## The time bound -/

theorem lt_2pow : ∀ n : Nat, n < 2 ^ n
  | 0 => by decide
  | n + 1 => by
    have := lt_2pow n
    have h : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [Nat.pow_succ]
    rw [h]
    generalize 2 ^ n = P at this ⊢
    omega

theorem pv_bound (n k Z T Q P S t : Nat) (hQ : 128 * (n + 2) ≤ Q) (hT : T ≤ Q) (hZ : Z ≤ Q)
    (hk : k ≤ Q) (hP : P ≤ k * (16 * T + 2) + 1) (hS : S ≤ 2 * T + 3 * Z + 10)
    (ht : t ≤ 12 * n + 13 + P + T * (S + 2) + 2 * T) :
    8 * (2 * n + 4) + 16 * (5 + 3) + 40 * t * (2 * n + 4 + 2 * (5 + 3) + 2 * t + 2) ≤ pw Q 18 := by
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
  have ht' : t ≤ pw Q 7 := by
    generalize k * (16 * T + 2) = K1 at hP c5
    generalize T * (S + 2) = K2 at ht c5
    generalize pw Q 7 = P7 at c5 ⊢
    clear a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b5' b6 c1 c2 c3 c4
    omega
  have w1 : 2 * n + 22 ≤ pw Q 7 := qup hQ1 (q1 (by omega)) (by decide)
  have w2 : 2 * t ≤ pw Q 8 := qmul (q1 hQ2) ht' rfl
  have w3 : 2 * n + 22 + 2 * t ≤ pw Q 9 := qadd hQ2 (qup hQ1 w1 (by decide)) w2 rfl
  have w : 2 * n + 4 + 2 * (5 + 3) + 2 * t + 2 ≤ pw Q 9 := by
    generalize pw Q 9 = P9 at w3 ⊢
    omega
  have v : 40 * t ≤ pw Q 8 := qmul (q1 (show 40 ≤ Q by omega)) ht' rfl
  have pr : 40 * t * (2 * n + 4 + 2 * (5 + 3) + 2 * t + 2) ≤ pw Q 17 := qmul v w rfl
  have li : 8 * (2 * n + 4) + 16 * (5 + 3) ≤ pw Q 17 := qup hQ1 (q1 (by omega)) (by decide)
  exact qadd hQ2 li pr rfl

theorem pv_lt (M : Mach) (k n t a : Nat) (ha : a = 2 * n + 4) (ht : t ≤ pvB M k n 0) :
    8 * a + 16 * (5 + 3) + 40 * t * (a + 2 * (5 + 3) + 2 * t + 2) <
      (n + 2) ^ (18 * (k + qm M + 8) + 1) := by
  subst ha
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
  have ht' : t ≤ 12 * n + 13 + powB (n + 2) k + (n + 2) ^ k * (sB M ((n + 2) ^ k) + 2) +
      2 * (n + 2) ^ k := by
    unfold pvB at ht
    generalize (n + 2) ^ k * (sB M ((n + 2) ^ k) + 2) = K at ht ⊢
    generalize (n + 2) ^ k = T at ht ⊢
    generalize powB (n + 2) k = B at ht ⊢
    clear hP hQ hT hZ hk hS
    omega
  have h := pv_bound n k (qm M) ((n + 2) ^ k) _ (powB (n + 2) k) (sB M ((n + 2) ^ k)) t
    hQ hT hZ hk hP hS ht'
  rw [pw_eq, ← Nat.pow_mul] at h
  refine Nat.lt_of_le_of_lt h (Nat.pow_lt_pow_right (Nat.lt_of_lt_of_le (by decide)
    (Nat.le_add_left 2 n)) ?_)
  clear h hP hQ hT hZ hk hS ht' ht
  generalize qm M = Z
  omega

/-! ## `P ⊆ NP` -/

theorem InP_InNP {A : List Bool → Prop} (h : InP A) : InNP A := by
  obtain ⟨M, k, hM⟩ := h
  refine ⟨vm 5 (PV M k), 18 * (k + qm M + 8) + 1, 0, fun x => ?_⟩
  obtain ⟨b, hb, hA⟩ := hM x
  have hz : zexec M ((x.length + 2) ^ k) 0 [] x = some b := by
    rw [← exec_z, ← inTape_z]; exact hb
  obtain ⟨S', ⟨t, ht, hE⟩, hiff⟩ := pv_ok M k x []
  have hE' : Exec (PV M k) (x :: [] :: List.replicate (5 + 1) []) S' t := hE
  have hans : S'.getD 0 [] ≠ [] ↔ b = true := by simp only [hiff, hz, Option.getD_some]
  have hl : (lay [x, []]).length = 2 * x.length + 4 := by rw [length_lay2]; simp
  constructor
  · intro hx
    refine ⟨[], Nat.zero_le _, ?_⟩
    rw [pairTape_lay, vm_ok 5 (ok_PV M k) hE' _ (pv_lt M k x.length t _ hl ht)]
    exact congrArg some (decide_eq_true (hans.mpr (hA.mpr hx)))
  · rintro ⟨c, hc, he⟩
    rw [Nat.zero_mul] at hc
    have hc0 : c = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hc)
    subst hc0
    let B := 8 * (lay [x, []]).length + 16 * (5 + 3) +
      40 * t * ((lay [x, []]).length + 2 * (5 + 3) + 2 * t + 2)
    have h1 := exec_mono _ _ _ _ _ _ he (max ((x.length + 2) ^ (18 * (k + qm M + 8) + 1)) (B + 1))
      (Nat.le_max_left _ _)
    rw [pairTape_lay, vm_ok 5 (ok_PV M k) hE' (max ((x.length + 2) ^ (18 * (k + qm M + 8) + 1)) (B + 1))
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _))] at h1
    exact hA.mp (hans.mp (of_decide_eq_true (Option.some.inj h1)))

end ZP.Cx
