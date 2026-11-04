module

public import ZP.Clock

@[expose] public section

/-!
# The verifier body

`BODY V k m` runs on twelve stacks `[x, c, [], …, []]`. It checks
`|c| ≤ (|x| + 2) ^ k · m`, builds the pair tape `lay [x, c]`, runs `SIM V` for
`(|x| + 2) ^ k` steps and leaves the answer on stack 0 (`body_ok`).

Programs written for eight stacks run unchanged with more stacks above them
(`Exec.frame`).
-/

namespace ZP.Cx

/-! ## Framing -/

theorem getD_app {S Y : List (List Bool)} {i : Nat} (h : i < S.length) :
    (S ++ Y).getD i [] = S.getD i [] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem set_app : ∀ (S Y : List (List Bool)) (i : Nat) (v : List Bool), i < S.length →
    (S ++ Y).set i v = S.set i v ++ Y
  | [], _, _, _, h => by simp at h
  | _ :: _, _, 0, _, _ => rfl
  | a :: S, Y, i + 1, v, h => by
    show a :: (S ++ Y).set i v = a :: (S.set i v ++ Y)
    rw [set_app S Y i v (by simp at h; omega)]

theorem Exec.frame {c : Cmd} {S S' : List (List Bool)} {t : Nat} (h : Exec c S S' t) :
    ∀ k, Ok k c → k ≤ S.length → ∀ Y, Exec c (S ++ Y) (S' ++ Y) t := by
  induction h with
  | @push i b S =>
    intro k hok hk Y
    have hi : i < S.length := Nat.lt_of_lt_of_le hok hk
    rw [← set_app S Y i _ hi, ← getD_app (Y := Y) hi]
    exact Exec.push
  | @pop i S =>
    intro k hok hk Y
    have hi : i < S.length := Nat.lt_of_lt_of_le hok hk
    rw [← set_app S Y i _ hi, ← getD_app (Y := Y) hi]
    exact Exec.pop
  | @cs i pe pf pt S S' t h ih =>
    intro k hok hk Y
    obtain ⟨hi, ha, hb, hc⟩ := hok
    refine Exec.cs ?_
    rw [getD_app (Nat.lt_of_lt_of_le hi hk)]
    exact ih k (ok_sel k pe pf pt ha hb hc _) hk Y
  | seq h1 h2 ih1 ih2 =>
    intro k hok hk Y
    exact Exec.seq (ih1 k hok.1 hk Y) (ih2 k hok.2 (by rw [h1.len]; exact hk) Y)
  | @whT i me mf mt p S S1 S2 t1 t2 hm h1 h2 ih1 ih2 =>
    intro k hok hk Y
    refine Exec.whT ?_ (ih1 k hok.2 hk Y) (ih2 k hok (by rw [h1.len]; exact hk) Y)
    rw [getD_app (Nat.lt_of_lt_of_le hok.1 hk)]
    exact hm
  | @whF i me mf mt p S hm =>
    intro k hok hk Y
    refine Exec.whF ?_
    rw [getD_app (Nat.lt_of_lt_of_le hok.1 hk)]
    exact hm
  | skip =>
    intro _ _ _ Y
    exact Exec.skip

theorem ExecB.frame {c : Cmd} {S S' : List (List Bool)} {B k : Nat} (h : ExecB c S S' B)
    (hok : Ok k c) (hk : k ≤ S.length) (Y : List (List Bool)) : ExecB c (S ++ Y) (S' ++ Y) B :=
  let ⟨t, ht, he⟩ := h
  ⟨t, ht, he.frame k hok hk Y⟩

theorem Ok.mono {k k' : Nat} (h : k ≤ k') : ∀ c : Cmd, Ok k c → Ok k' c
  | .push _ _, hc => Nat.lt_of_lt_of_le hc h
  | .pop _, hc => Nat.lt_of_lt_of_le hc h
  | .cs _ a b c, hc => ⟨Nat.lt_of_lt_of_le hc.1 h, Ok.mono h a hc.2.1, Ok.mono h b hc.2.2.1,
      Ok.mono h c hc.2.2.2⟩
  | .seq p q, hc => ⟨Ok.mono h p hc.1, Ok.mono h q hc.2⟩
  | .wh _ _ _ _ p, hc => ⟨Nat.lt_of_lt_of_le hc.1 h, Ok.mono h p hc.2⟩
  | .skip, _ => trivial

theorem ok_CLK (k : Nat) : Ok 8 (CLK k) :=
  ⟨okb_ok 8 LEN (by decide), okb_ok 8 _ (by decide), ok_POW k⟩

/-! ## Small programs -/

def pushK (i : Nat) : Nat → Cmd
  | 0 => .skip
  | n + 1 => .seq (.push i true) (pushK i n)

theorem ok_pushK {k i : Nat} (h : i < k) : ∀ n, Ok k (pushK i n)
  | 0 => trivial
  | n + 1 => ⟨h, ok_pushK h n⟩

theorem pushK_ok {R L Q C A D T : List Bool} {Y : List (List Bool)} : ∀ (n : Nat) (N : List Bool),
    ExecB (pushK 5 n) (WS R L Q C A N D T ++ Y)
      (WS R L Q C A (List.replicate n true ++ N) D T ++ Y) (n + 1)
  | 0, N => ExecB.skip.to rfl (Nat.le_refl _)
  | n + 1, N => by
    have ih := pushK_ok (R := R) (L := L) (Q := Q) (C := C) (A := A) (D := D) (T := T) (Y := Y)
      n (true :: N)
    refine (ExecB.push.seq ih).to ?_ (by omega)
    simp [WS, List.replicate_succ']

/-- Compare: move stack 8 onto stack 9, one cell of stack 3 per bit; stack 10 counts
the excess. -/
def CMP : Cmd := .wh 8 false true true (.seq (mv1 8 9) (.cs 3 (.push 10 true) (.pop 3) (.pop 3)))

theorem cmp_ok {R L Q A N D T Z : List Bool} : ∀ (u : List Bool) (c : Nat) (v f : List Bool),
    ExecB CMP (WS R L Q (List.replicate c true) A N D T ++ [u, v, f, Z])
      (WS R L Q (List.replicate (c - u.length) true) A N D T ++
        [[], u.reverse ++ v, List.replicate (u.length - c) true ++ f, Z]) (6 * u.length + 1)
  | [], c, v, f => ExecB.to (ExecB.whF (by rfl)) (by simp) (by omega)
  | b :: u, c, v, f => by
    have h1 : ExecB (mv1 8 9) (WS R L Q (List.replicate c true) A N D T ++ [b :: u, v, f, Z])
        (WS R L Q (List.replicate c true) A N D T ++ [u, b :: v, f, Z]) 3 :=
      mv1_cons (b := b) (u := u) (by decide) rfl
    cases c with
    | zero =>
      have h2 : ExecB (Cmd.cs 3 (.push 10 true) (.pop 3) (.pop 3))
          (WS R L Q (List.replicate 0 true) A N D T ++ [u, b :: v, f, Z])
          (WS R L Q (List.replicate 0 true) A N D T ++ [u, b :: v, true :: f, Z]) 2 :=
        ExecB.cs (ExecB.push.to rfl (Nat.le_refl _))
      have ih := cmp_ok (R := R) (L := L) (Q := Q) (A := A) (N := N) (D := D) (T := T) (Z := Z)
        u 0 (b :: v) (true :: f)
      refine (ExecB.whT (by cases b <;> rfl) (h1.seq h2) ih).to ?_ ?_
      · simp [WS, List.replicate_succ']
      · simp only [List.length_cons]; omega
    | succ c =>
      have h2 : ExecB (Cmd.cs 3 (.push 10 true) (.pop 3) (.pop 3))
          (WS R L Q (List.replicate (c + 1) true) A N D T ++ [u, b :: v, f, Z])
          (WS R L Q (List.replicate c true) A N D T ++ [u, b :: v, f, Z]) 2 :=
        ExecB.cs (ExecB.pop.to rfl (Nat.le_refl _))
      have ih := cmp_ok (R := R) (L := L) (Q := Q) (A := A) (N := N) (D := D) (T := T) (Z := Z)
        u c (b :: v) f
      refine (ExecB.whT (by cases b <;> rfl) (h1.seq h2) ih).to ?_ ?_
      · simp [WS]
      · simp only [List.length_cons]; omega

/-- Encode: pop stack `i` bit by bit, pushing `1 b` on stack `j`. -/
def encb (i j : Nat) (b : Bool) : Cmd := .seq (.pop i) (.seq (.push j true) (.push j b))

def encL (i j : Nat) : Cmd := .wh i false true true (.cs i .skip (encb i j false) (encb i j true))

theorem encL_ok {i j : Nat} (hij : i ≠ j) : ∀ (u : List Bool) (S : List (List Bool)),
    i < S.length → j < S.length → S.getD i [] = u →
      ExecB (encL i j) S ((S.set i []).set j ((encR u).reverse ++ S.getD j [])) (6 * u.length + 1)
  | [], S, hi, hj, h => by
    refine (ExecB.whF (by rw [h]; rfl)).to ?_ (by omega)
    stk_eq
  | b :: u, S, hi, hj, h => by
    have hp : ExecB (encb i j b) S ((S.set i u).set j (b :: true :: S.getD j [])) 3 := by
      refine (ExecB.pop.seq (ExecB.push.seq ExecB.push)).to ?_ (Nat.le_refl _)
      rw [h, List.tail_cons]
      stk_eq
    have hp' : ExecB (sel (S.getD i []) .skip (encb i j false) (encb i j true)) S
        ((S.set i u).set j (b :: true :: S.getD j [])) 3 := by
      rw [h]; cases b <;> exact hp
    have h2 := encL_ok hij u ((S.set i u).set j (b :: true :: S.getD j [])) (by simpa using hi)
      (by simpa using hj) (by rw [getD_set_ne _ hij, getD_set_eq _ hi])
    refine (ExecB.whT (by rw [h]; cases b <;> rfl) (ExecB.cs hp') h2).to ?_
      (by simp only [List.length_cons]; omega)
    stk_eq

/-! ## The program -/

def PRE (k m : Nat) : Cmd :=
  .seq (mv 1 8) (.seq (CLK k) (.seq (clr 5) (.seq (pushK 5 m) (.seq MUL (.seq CMP
    (.seq (clr 3) (clr 5)))))))

def BMAIN (V : Mach) (k : Nat) : Cmd :=
  .seq (CLK k) (.seq (clr 5) (.seq (encL 0 6) (.seq (.seq (.push 6 false) (.push 6 true))
    (.seq (encL 9 6) (.seq (.seq (.push 6 false) (.push 6 true)) (.seq (mv 6 0)
      (.seq (SIM V) (.seq (clr 0) (mv 4 0)))))))))

def BODY (V : Mach) (k m : Nat) : Cmd := .seq (PRE k m) (.cs 10 (BMAIN V k) (clr 0) (clr 0))

theorem ok_BODY (V : Mach) (k m : Nat) : Ok 12 (BODY V k m) :=
  ⟨⟨okb_ok 12 (mv 1 8) (by decide), Ok.mono (by decide) _ (ok_CLK k), okb_ok 12 (clr 5) (by decide),
      ok_pushK (by decide) m, okb_ok 12 MUL (by decide), okb_ok 12 CMP (by decide),
      okb_ok 12 (clr 3) (by decide), okb_ok 12 (clr 5) (by decide)⟩,
    (by decide : 10 < 12),
    ⟨Ok.mono (by decide) _ (ok_CLK k), okb_ok 12 (clr 5) (by decide), okb_ok 12 (encL 0 6) (by decide),
      okb_ok 12 (.seq (.push 6 false) (.push 6 true)) (by decide), okb_ok 12 (encL 9 6) (by decide),
      okb_ok 12 (.seq (.push 6 false) (.push 6 true)) (by decide), okb_ok 12 (mv 6 0) (by decide),
      ok_SIM (by decide) V, okb_ok 12 (clr 0) (by decide), okb_ok 12 (mv 4 0) (by decide)⟩,
    okb_ok 12 (clr 0) (by decide), okb_ok 12 (clr 0) (by decide)⟩

def preB (k m n c : Nat) : Nat :=
  4 * c + 1 + (10 * n + 2 + (3 + powB (n + 2) k) + (2 * (n + 2) + 1 + (m + 1 +
    ((n + 2) ^ k * (8 * m + 4) + 4 * ((n + 2) ^ k * m) + 2 + (6 * c + 1 +
      (2 * ((n + 2) ^ k * m) + 1 + (2 * m + 1)))))))

theorem bpre_ok (k m : Nat) (x c0 : List Bool) :
    ExecB (PRE k m) (WS x c0 [] [] [] [] [] [] ++ [[], [], [], []])
      (WS x [] [] [] [] [] [] [] ++
        [[], c0, List.replicate (c0.length - (x.length + 2) ^ k * m) true, []])
      (preB k m x.length c0.length) := by
  have e1 : ExecB (mv 1 8) (WS x c0 [] [] [] [] [] [] ++ [[], [], [], []])
      (WS x [] [] [] [] [] [] [] ++ [c0.reverse, [], [], []]) (4 * c0.length + 1) :=
    (mv_ok (i := 1) (j := 8) (by decide) c0 (WS x c0 [] [] [] [] [] [] ++ [[], [], [], []])
      (by simp [WS]) (by simp [WS]) rfl).to (by simp [WS]) (Nat.le_refl _)
  have e2 := (clk_ok (L := []) x k).frame (ok_CLK k) (by simp [WS]) [c0.reverse, [], [], []]
  have e3 : ExecB (clr 5)
      (WS x [] [] (List.replicate ((x.length + 2) ^ k) true) [] (List.replicate (x.length + 2) true)
        [] [] ++ [c0.reverse, [], [], []])
      (WS x [] [] (List.replicate ((x.length + 2) ^ k) true) [] [] [] [] ++ [c0.reverse, [], [], []])
      (2 * (x.length + 2) + 1) :=
    (clr_ok (i := 5) (List.replicate (x.length + 2) true) _ (by simp [WS]) rfl).to rfl (by simp)
  have e4 := pushK_ok (R := x) (L := []) (Q := []) (C := List.replicate ((x.length + 2) ^ k) true)
    (A := []) (D := []) (T := []) (Y := [c0.reverse, [], [], []]) m []
  have e5 := (mul_ok (R := x) (L := []) (Q := []) (A := []) m ((x.length + 2) ^ k)).frame
    (okb_ok 8 MUL (by decide)) (by simp [WS]) [c0.reverse, [], [], []]
  have e5' : ExecB MUL
      (WS x [] [] (List.replicate ((x.length + 2) ^ k) true) [] (List.replicate m true ++ []) [] [] ++
        [c0.reverse, [], [], []])
      (WS x [] [] (List.replicate ((x.length + 2) ^ k * m) true) [] (List.replicate m true) [] [] ++
        [c0.reverse, [], [], []])
      ((x.length + 2) ^ k * (8 * m + 4) + 4 * ((x.length + 2) ^ k * m) + 2) := by
    rw [List.append_nil]; exact e5
  have e6 := cmp_ok (R := x) (L := []) (Q := []) (A := []) (N := List.replicate m true) (D := [])
    (T := []) (Z := []) c0.reverse ((x.length + 2) ^ k * m) [] []
  have e7 : ExecB (clr 3)
      (WS x [] [] (List.replicate ((x.length + 2) ^ k * m - c0.reverse.length) true) []
        (List.replicate m true) [] [] ++
        [[], c0.reverse.reverse ++ [], List.replicate (c0.reverse.length - (x.length + 2) ^ k * m) true
          ++ [], []])
      (WS x [] [] [] [] (List.replicate m true) [] [] ++
        [[], c0.reverse.reverse ++ [], List.replicate (c0.reverse.length - (x.length + 2) ^ k * m) true
          ++ [], []])
      (2 * ((x.length + 2) ^ k * m) + 1) :=
    (clr_ok (i := 3) (List.replicate ((x.length + 2) ^ k * m - c0.reverse.length) true) _
      (by simp [WS]) rfl).to rfl (by
        simp only [List.length_replicate, List.length_reverse]
        exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.sub_le _ _)) 1)
  have e8 : ExecB (clr 5)
      (WS x [] [] [] [] (List.replicate m true) [] [] ++
        [[], c0.reverse.reverse ++ [], List.replicate (c0.reverse.length - (x.length + 2) ^ k * m) true
          ++ [], []])
      (WS x [] [] [] [] [] [] [] ++
        [[], c0, List.replicate (c0.length - (x.length + 2) ^ k * m) true, []])
      (2 * m + 1) :=
    (clr_ok (i := 5) (List.replicate m true) _ (by simp [WS]) rfl).to (by simp [WS]) (by simp)
  refine (e1.seq (e2.seq (e3.seq (e4.seq (e5'.seq (e6.seq (e7.seq e8))))))).to rfl ?_
  unfold preB
  simp only [List.length_reverse]
  generalize (x.length + 2) ^ k * (8 * m + 4) = K1
  generalize (x.length + 2) ^ k * m = K2
  generalize powB (x.length + 2) k = B
  omega

def mainB (V : Mach) (k n c : Nat) : Nat :=
  10 * n + 2 + (3 + powB (n + 2) k) + (2 * (n + 2) + 1 + (6 * n + 1 + (2 + (6 * c + 1 + (2 +
    (4 * (2 * n + 2 * c + 4) + 1 + ((n + 2) ^ k * (sB V ((n + 2) ^ k) + 2) + 1 +
      (2 * (2 * n + 2 * c + 4 + (n + 2) ^ k) + 1 + 5))))))))

theorem lay2_rev (x c0 : List Bool) :
    (true :: false :: ((encR c0).reverse ++ true :: false :: (encR x).reverse)).reverse =
      lay [x, c0] := by
  simp

theorem main_ok (V : Mach) (k : Nat) (x c0 : List Bool) :
    ∃ S', ExecB (BMAIN V k) (WS x [] [] [] [] [] [] [] ++ [[], c0, [], []]) S'
        (mainB V k x.length c0.length) ∧
      (S'.getD 0 [] ≠ [] ↔ (zexec V ((x.length + 2) ^ k) 0 [] (lay [x, c0])).getD false = true) := by
  have e1 := (clk_ok (L := []) x k).frame (ok_CLK k) (by simp [WS]) [[], c0, [], []]
  have e2 : ExecB (clr 5)
      (WS x [] [] (List.replicate ((x.length + 2) ^ k) true) [] (List.replicate (x.length + 2) true)
        [] [] ++ [[], c0, [], []])
      (WS x [] [] (List.replicate ((x.length + 2) ^ k) true) [] [] [] [] ++ [[], c0, [], []])
      (2 * (x.length + 2) + 1) :=
    (clr_ok (i := 5) (List.replicate (x.length + 2) true) _ (by simp [WS]) rfl).to rfl (by simp)
  have e3 : ExecB (encL 0 6)
      (WS x [] [] (List.replicate ((x.length + 2) ^ k) true) [] [] [] [] ++ [[], c0, [], []])
      (WS [] [] [] (List.replicate ((x.length + 2) ^ k) true) [] [] (encR x).reverse [] ++
        [[], c0, [], []]) (6 * x.length + 1) :=
    (encL_ok (i := 0) (j := 6) (by decide) x _ (by simp [WS]) (by simp [WS]) rfl).to
      (by simp [WS]) (Nat.le_refl _)
  have e4 : ExecB (.seq (.push 6 false) (.push 6 true))
      (WS [] [] [] (List.replicate ((x.length + 2) ^ k) true) [] [] (encR x).reverse [] ++
        [[], c0, [], []])
      (WS [] [] [] (List.replicate ((x.length + 2) ^ k) true) [] []
        (true :: false :: (encR x).reverse) [] ++ [[], c0, [], []]) 2 :=
    (ExecB.push.seq ExecB.push).to rfl (Nat.le_refl _)
  have e5 : ExecB (encL 9 6)
      (WS [] [] [] (List.replicate ((x.length + 2) ^ k) true) [] []
        (true :: false :: (encR x).reverse) [] ++ [[], c0, [], []])
      (WS [] [] [] (List.replicate ((x.length + 2) ^ k) true) [] []
        ((encR c0).reverse ++ true :: false :: (encR x).reverse) [] ++ [[], [], [], []])
      (6 * c0.length + 1) :=
    (encL_ok (i := 9) (j := 6) (by decide) c0 _ (by simp [WS]) (by simp [WS]) rfl).to
      (by simp [WS]) (Nat.le_refl _)
  have e6 : ExecB (.seq (.push 6 false) (.push 6 true))
      (WS [] [] [] (List.replicate ((x.length + 2) ^ k) true) [] []
        ((encR c0).reverse ++ true :: false :: (encR x).reverse) [] ++ [[], [], [], []])
      (WS [] [] [] (List.replicate ((x.length + 2) ^ k) true) [] []
        (true :: false :: ((encR c0).reverse ++ true :: false :: (encR x).reverse)) [] ++
        [[], [], [], []]) 2 :=
    (ExecB.push.seq ExecB.push).to rfl (Nat.le_refl _)
  have hW : (true :: false :: ((encR c0).reverse ++ true :: false :: (encR x).reverse)).length =
      2 * x.length + 2 * c0.length + 4 := by
    simp [length_encR]; omega
  have e7 : ExecB (mv 6 0)
      (WS [] [] [] (List.replicate ((x.length + 2) ^ k) true) [] []
        (true :: false :: ((encR c0).reverse ++ true :: false :: (encR x).reverse)) [] ++
        [[], [], [], []])
      (WS (lay [x, c0]) [] [] (List.replicate ((x.length + 2) ^ k) true) [] [] [] [] ++
        [[], [], [], []]) (4 * (2 * x.length + 2 * c0.length + 4) + 1) := by
    refine (mv_ok (i := 6) (j := 0) (by decide)
      (true :: false :: ((encR c0).reverse ++ true :: false :: (encR x).reverse))
      (WS [] [] [] (List.replicate ((x.length + 2) ^ k) true) [] []
        (true :: false :: ((encR c0).reverse ++ true :: false :: (encR x).reverse)) [] ++
        [[], [], [], []]) (by simp [WS]) (by simp [WS]) rfl).to ?_
      (Nat.le_of_eq (by rw [hW]))
    rw [← lay2_rev x c0]
    simp [WS]
  obtain ⟨R', L', Q', hl, e8⟩ := sim_ok V [[], [], [], [], [], [], []] ((x.length + 2) ^ k) 0 []
    (lay [x, c0]) (Nat.zero_le _)
  have e8' : ExecB (SIM V)
      (WS (lay [x, c0]) [] [] (List.replicate ((x.length + 2) ^ k) true) [] [] [] [] ++
        [[], [], [], []])
      (SV R' L' Q' [] (ansOf ((zexec V ((x.length + 2) ^ k) 0 [] (lay [x, c0])).getD false))
        [[], [], [], [], [], [], []])
      ((x.length + 2) ^ k * (sB V ((x.length + 2) ^ k) + 2) + 1) := e8
  generalize (zexec V ((x.length + 2) ^ k) 0 [] (lay [x, c0])).getD false = b at e8' ⊢
  have e9 : ExecB (clr 0) (SV R' L' Q' [] (ansOf b) [[], [], [], [], [], [], []])
      (SV [] L' Q' [] (ansOf b) [[], [], [], [], [], [], []]) (2 * R'.length + 1) :=
    (clr_ok (i := 0) R' _ (by simp [SV]) rfl).to rfl (Nat.le_refl _)
  have e10 := mv_ok (i := 4) (j := 0) (by decide) (ansOf b)
    (SV [] L' Q' [] (ansOf b) [[], [], [], [], [], [], []]) (by simp [SV]) (by simp [SV]) rfl
  refine ⟨_, (e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8'.seq
    (e9.seq e10))))))))).to rfl ?_, ?_⟩
  · have := length_ansOf b
    rw [length_lay2] at hl
    simp only [List.length_nil, Nat.add_zero] at hl
    unfold mainB
    generalize (x.length + 2) ^ k * (sB V ((x.length + 2) ^ k) + 2) = K
    generalize (x.length + 2) ^ k = T at hl ⊢
    generalize powB (x.length + 2) k = B
    omega
  · cases b <;> simp [SV, ansOf]

def bodyB (V : Mach) (k m n c : Nat) : Nat := preB k m n c + (mainB V k n c + 2 * n + 2)

theorem body_ok (V : Mach) (k m : Nat) (x c0 : List Bool) :
    ∃ S', ExecB (BODY V k m) (x :: c0 :: List.replicate 10 []) S'
        (bodyB V k m x.length c0.length) ∧
      (S'.getD 0 [] ≠ [] ↔ c0.length ≤ (x.length + 2) ^ k * m ∧
        (zexec V ((x.length + 2) ^ k) 0 [] (lay [x, c0])).getD false = true) := by
  have e1 := bpre_ok k m x c0
  generalize (x.length + 2) ^ k * m = P at e1 ⊢
  by_cases hc : c0.length ≤ P
  · have h0 : c0.length - P = 0 := by omega
    rw [h0] at e1
    obtain ⟨S', e2, hS'⟩ := main_ok V k x c0
    have e2' : ExecB (.cs 10 (BMAIN V k) (clr 0) (clr 0))
        (WS x [] [] [] [] [] [] [] ++ [[], c0, List.replicate 0 true, []]) S'
        (mainB V k x.length c0.length + 1) := ExecB.cs e2
    refine ⟨S', (e1.seq e2').to rfl (by unfold bodyB; omega), ?_⟩
    rw [hS']
    exact ⟨fun h => ⟨hc, h⟩, fun h => h.2⟩
  · obtain ⟨d, hd⟩ : ∃ d, c0.length - (x.length + 2) ^ k * m = d + 1 := ⟨_, (by omega : _ = _ - 1 + 1)⟩
    rw [hd] at e1
    have e2 : ExecB (clr 0) (WS x [] [] [] [] [] [] [] ++ [[], c0, List.replicate (d + 1) true, []])
        (WS [] [] [] [] [] [] [] [] ++ [[], c0, List.replicate (d + 1) true, []])
        (2 * x.length + 1) :=
      (clr_ok (i := 0) x _ (by simp [WS]) rfl).to rfl (Nat.le_refl _)
    have e2' : ExecB (.cs 10 (BMAIN V k) (clr 0) (clr 0))
        (WS x [] [] [] [] [] [] [] ++ [[], c0, List.replicate (d + 1) true, []])
        (WS [] [] [] [] [] [] [] [] ++ [[], c0, List.replicate (d + 1) true, []])
        (2 * x.length + 1 + 1) := ExecB.cs e2
    refine ⟨_, (e1.seq e2').to rfl (by unfold bodyB; omega), ?_⟩
    constructor
    · intro h; exact absurd rfl h
    · intro h; exact absurd h.1 hc

end ZP.Cx
