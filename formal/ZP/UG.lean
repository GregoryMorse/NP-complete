module

public import ZP.Lib

@[expose] public section

/-!
# The guest interpreter as a stack program

`UG` runs on thirteen stacks `[s, c, ...]` and leaves a nonempty stack 0 exactly
when `|c| = |s| + 1` and the guest program `s` accepts `c` within `|s| + 1` steps
(`ug_ok`). Stack roles: 0 input, 1 guest tape from the head on, 2 the cyclic code
`R`, 3 scratch, 4 guest tape left of the head, 5 counter, 6 clock, 7 and 8 the
length check, 9 and 10 the first two bits of `R`, 11 the answer, 12 scratch.
-/

namespace ZP.Cx

/-- The state with the two scratch stacks empty. -/
def U (x gr r gl k clk e bad fw fd ans : List Bool) : List (List Bool) :=
  [x, gr, r, [], gl, k, clk, e, bad, fw, fd, ans, []]

def ansOf (b : Bool) : List Bool := if b then [true] else []

def ROT : Cmd := rotq 2 3 12
def ROTK : Cmd := rotk 2 3 5
def RL : Cmd := .wh 5 false true true (.seq (.pop 5) ROT)
def IOTA : Cmd := .cs 1 .skip ROT (.seq ROT ROT)
def HALT : Cmd := .seq (.cs 9 .skip .skip (.push 11 true)) (.seq (clr 6) (.seq (mv1 10 2) (mv1 9 2)))
def WR : Cmd := .cs 9 .skip (.push 1 false) (.push 1 true)
def MOVE : Cmd := .cs 10 .skip (mv1 4 1) (mv1 1 4)
def CONT : Cmd :=
  .seq (.pop 1) (.seq WR (.seq MOVE (.seq (mv1 10 2) (.seq (mv1 9 2) (.seq ROTK (.seq ROT RL))))))
def STEP : Cmd := .seq IOTA (.seq (mv1 2 9) (.seq (mv1 2 10) (.cs 2 HALT HALT CONT)))
def MAIN : Cmd := .wh 6 false true true (.seq (.pop 6) STEP)

/-! ## Rotations on the interpreter state -/

theorem rot_U {x gr R gl k clk e bad fw fd ans : List Bool} (h0 : false ∈ R) :
    ExecB ROT (U x gr R gl k clk e bad fw fd ans) (U x gr (rot R) gl k clk e bad fw fd ans)
      (rB R.length) :=
  (rotq_ok (r := 2) (t := 3) (j := 12) (by decide) (by decide) (by decide) (by simp [U])
    (by simp [U]) (by simp [U]) h0 rfl rfl rfl).to rfl (Nat.le_refl _)

theorem rotk_U {x gr R gl k clk e bad fw fd ans : List Bool} (h0 : false ∈ R) :
    ExecB ROTK (U x gr R gl k clk e bad fw fd ans)
      (U x gr (rot R) gl (List.replicate (entryOnes R) true ++ k) clk e bad fw fd ans)
      ((R.length + 3) * (8 * R.length + 8) + 1) :=
  (rotk_ok (r := 2) (t := 3) (k := 5) (by decide) (by decide) (by decide) (by simp [U])
    (by simp [U]) (by simp [U]) h0 rfl rfl).to rfl (Nat.le_refl _)

theorem rl_U {x gr gl clk e bad fw fd ans : List Bool} : ∀ (m : Nat) (R : List Bool), false ∈ R →
    ExecB RL (U x gr R gl (List.replicate m true ++ []) clk e bad fw fd ans)
      (U x gr (rotN m R) gl [] clk e bad fw fd ans) (m * (rB R.length + 2) + 1)
  | 0, R, _ => ExecB.to (ExecB.whF (by rfl)) rfl (by omega)
  | m + 1, R, h0 => by
    have b1 : ExecB (.pop 5) (U x gr R gl (List.replicate (m + 1) true ++ []) clk e bad fw fd ans)
        (U x gr R gl (List.replicate m true ++ []) clk e bad fw fd ans) 1 :=
      ExecB.pop.to rfl (Nat.le_refl _)
    have b2 := rot_U (x := x) (gr := gr) (gl := gl) (k := List.replicate m true ++ []) (clk := clk)
      (e := e) (bad := bad) (fw := fw) (fd := fd) (ans := ans) h0
    have ih := rl_U (x := x) (gr := gr) (gl := gl) (clk := clk) (e := e) (bad := bad) (fw := fw)
      (fd := fd) (ans := ans) m (rot R) (mem_rot h0)
    rw [length_rot] at ih
    refine (ExecB.whT (by rfl) (b1.seq b2) ih).to rfl ?_
    have hx := Nat.add_mul m 1 (rB R.length + 2)
    rw [Nat.one_mul] at hx
    omega

theorem iota_U {x gr R gl k clk e bad fw fd ans : List Bool} (h0 : false ∈ R) :
    ExecB IOTA (U x gr R gl k clk e bad fw fd ans)
      (U x gr (rotN (iota gr.head?) R) gl k clk e bad fw fd ans) (2 * rB R.length + 1) := by
  match gr with
  | [] => exact ExecB.to (ExecB.cs (by exact ExecB.skip)) rfl (by omega)
  | false :: g => exact ExecB.to (ExecB.cs (by exact rot_U h0)) rfl (by omega)
  | true :: g =>
    exact ExecB.to (ExecB.cs (by exact (rot_U h0).seq (rot_U (mem_rot h0)))) rfl
      (by rw [length_rot]; omega)

/-! ## One guest step -/

/-- The guest head writes `w` and moves right if `d`. -/
def gmove (d w : Bool) (gl gr : List Bool) : List Bool × List Bool :=
  if d then (w :: gl, gr.tail) else
    match gl with
    | [] => ([], w :: gr.tail)
    | b :: l => (l, b :: w :: gr.tail)

theorem gmove_ok (d w : Bool) (gl gr : List Bool) :
    ztape (gmove d w gl gr).1 (gmove d w gl gr).2 = write (ztape gl gr) gl.length w ∧
      (gmove d w gl gr).1.length = move d gl.length := by
  rw [ztape_write]
  cases d with
  | true => exact ⟨ztape_shift _ _ _, rfl⟩
  | false =>
    cases gl with
    | nil => exact ⟨rfl, rfl⟩
    | cons b l => exact ⟨(ztape_shift _ _ _).symm, by simp [gmove, move]⟩

def stepB (n T : Nat) : Nat := (n + 4) * (rB n + 2) + 2 * T + 40

theorem halt_U {x e bad gr gl clk rest fdl : List Bool} {w : Bool} (hf : fdl.length ≤ 1) :
    ExecB HALT (U x gr rest gl [] clk e bad [w] fdl [])
      (U x gr (w :: (fdl ++ rest)) gl [] [] e bad [] [] (ansOf w)) (2 * clk.length + 9) := by
  have h1 : ExecB (.cs 9 .skip .skip (.push 11 true)) (U x gr rest gl [] clk e bad [w] fdl [])
      (U x gr rest gl [] clk e bad [w] fdl (ansOf w)) 2 := by
    cases w
    · exact ExecB.cs ExecB.skip
    · exact ExecB.cs (ExecB.push.to rfl (Nat.le_refl _))
  have h2 : ExecB (clr 6) (U x gr rest gl [] clk e bad [w] fdl (ansOf w))
      (U x gr rest gl [] [] e bad [w] fdl (ansOf w)) (2 * clk.length + 1) :=
    (clr_ok clk _ (by simp [U]) rfl).to rfl (Nat.le_refl _)
  have h3 : ExecB (mv1 10 2) (U x gr rest gl [] [] e bad [w] fdl (ansOf w))
      (U x gr (fdl ++ rest) gl [] [] e bad [w] [] (ansOf w)) 3 := by
    match fdl, hf with
    | [], _ => exact (mv1_nil rfl).to rfl (by omega)
    | [d], _ => exact (mv1_cons (by decide) rfl).to rfl (Nat.le_refl _)
    | _ :: _ :: _, h => simp at h
  have h4 : ExecB (mv1 9 2) (U x gr (fdl ++ rest) gl [] [] e bad [w] [] (ansOf w))
      (U x gr (w :: (fdl ++ rest)) gl [] [] e bad [] [] (ansOf w)) 3 :=
    (mv1_cons (by decide) rfl).to rfl (Nat.le_refl _)
  exact (h1.seq (h2.seq (h3.seq h4))).to rfl (by omega)

theorem step_halt {x e bad R gl gr clk R1 : List Bool} (h0 : false ∈ R)
    (hR1 : rotN (iota gr.head?) R = R1) (h2 : R1.getD 2 false = false) :
    ExecB STEP (U x gr R gl [] clk e bad [] [] [])
      (U x gr R1 gl [] [] e bad [] [] (ansOf (R1.getD 0 false))) (stepB R.length clk.length) := by
  have a1 := iota_U (x := x) (gr := gr) (gl := gl) (k := []) (clk := clk) (e := e) (bad := bad)
    (fw := []) (fd := []) (ans := []) h0
  rw [hR1] at a1
  have hm : false ∈ R1 := by rw [← hR1]; exact mem_rotN _ h0
  have hb : 2 * rB R.length + 1 + 3 + 3 + 1 + (2 * clk.length + 9) ≤ stepB R.length clk.length := by
    have hx := Nat.add_mul R.length 4 (rB R.length + 2)
    unfold stepB; omega
  match R1, h2, hm with
  | [], _, hm => simp at hm
  | [w], _, _ =>
    have a2 : ExecB (mv1 2 9) (U x gr [w] gl [] clk e bad [] [] [])
        (U x gr [] gl [] clk e bad [w] [] []) 3 := (mv1_cons (by decide) rfl).to rfl (Nat.le_refl _)
    have a3 : ExecB (mv1 2 10) (U x gr [] gl [] clk e bad [w] [] [])
        (U x gr [] gl [] clk e bad [w] [] []) 3 := (mv1_nil rfl).to rfl (by omega)
    have a4 := halt_U (x := x) (e := e) (bad := bad) (gr := gr) (gl := gl) (clk := clk) (rest := [])
      (fdl := []) (w := w) (by simp)
    exact (a1.seq (a2.seq (a3.seq (ExecB.cs (by exact a4))))).to rfl (by omega)
  | w :: d :: rest, h2, _ =>
    have a2 : ExecB (mv1 2 9) (U x gr (w :: d :: rest) gl [] clk e bad [] [] [])
        (U x gr (d :: rest) gl [] clk e bad [w] [] []) 3 :=
      (mv1_cons (by decide) rfl).to rfl (Nat.le_refl _)
    have a3 : ExecB (mv1 2 10) (U x gr (d :: rest) gl [] clk e bad [w] [] [])
        (U x gr rest gl [] clk e bad [w] [d] []) 3 := (mv1_cons (by decide) rfl).to rfl (Nat.le_refl _)
    have a4 := halt_U (x := x) (e := e) (bad := bad) (gr := gr) (gl := gl) (clk := clk) (rest := rest)
      (fdl := [d]) (w := w) (by simp)
    have a5 : ExecB (.cs 2 HALT HALT CONT) (U x gr rest gl [] clk e bad [w] [d] [])
        (U x gr (w :: d :: rest) gl [] [] e bad [] [] (ansOf w)) (2 * clk.length + 9 + 1) := by
      match rest, h2 with
      | [], _ => exact ExecB.cs a4
      | false :: _, _ => exact ExecB.cs a4
      | true :: _, h => simp at h
    exact (a1.seq (a2.seq (a3.seq a5))).to rfl (by omega)

theorem step_cont {x e bad R gl gr clk : List Bool} {w d : Bool} {rest : List Bool}
    (h0 : false ∈ R) (hR1 : rotN (iota gr.head?) R = w :: d :: true :: rest) :
    ExecB STEP (U x gr R gl [] clk e bad [] [] [])
      (U x (gmove d w gl gr).2 (rotN (entryOnes (w :: d :: true :: rest) + 1)
        (rot (w :: d :: true :: rest))) (gmove d w gl gr).1 [] clk e bad [] [] [])
      (stepB R.length clk.length) := by
  have hn : (w :: d :: true :: rest).length = R.length := by rw [← hR1, length_rotN]
  have hm : false ∈ w :: d :: true :: rest := by rw [← hR1]; exact mem_rotN _ h0
  have a1 := iota_U (x := x) (gr := gr) (gl := gl) (k := []) (clk := clk) (e := e) (bad := bad)
    (fw := []) (fd := []) (ans := []) h0
  rw [hR1] at a1
  have a2 : ExecB (mv1 2 9) (U x gr (w :: d :: true :: rest) gl [] clk e bad [] [] [])
      (U x gr (d :: true :: rest) gl [] clk e bad [w] [] []) 3 :=
    (mv1_cons (by decide) rfl).to rfl (Nat.le_refl _)
  have a3 : ExecB (mv1 2 10) (U x gr (d :: true :: rest) gl [] clk e bad [w] [] [])
      (U x gr (true :: rest) gl [] clk e bad [w] [d] []) 3 :=
    (mv1_cons (by decide) rfl).to rfl (Nat.le_refl _)
  have c1 : ExecB (.pop 1) (U x gr (true :: rest) gl [] clk e bad [w] [d] [])
      (U x gr.tail (true :: rest) gl [] clk e bad [w] [d] []) 1 := ExecB.pop.to rfl (Nat.le_refl _)
  have c2 : ExecB WR (U x gr.tail (true :: rest) gl [] clk e bad [w] [d] [])
      (U x (w :: gr.tail) (true :: rest) gl [] clk e bad [w] [d] []) 2 := by
    cases w
    · exact ExecB.cs (ExecB.push.to rfl (Nat.le_refl _))
    · exact ExecB.cs (ExecB.push.to rfl (Nat.le_refl _))
  have c3 : ExecB MOVE (U x (w :: gr.tail) (true :: rest) gl [] clk e bad [w] [d] [])
      (U x (gmove d w gl gr).2 (true :: rest) (gmove d w gl gr).1 [] clk e bad [w] [d] []) 4 := by
    cases d with
    | true => exact ExecB.to (ExecB.cs (by exact mv1_cons (by decide) rfl)) rfl (by omega)
    | false =>
      cases gl with
      | nil => exact ExecB.to (ExecB.cs (by exact mv1_nil rfl)) rfl (by omega)
      | cons b l => exact ExecB.to (ExecB.cs (by exact mv1_cons (by decide) rfl)) rfl (by omega)
  have c4 : ExecB (mv1 10 2)
      (U x (gmove d w gl gr).2 (true :: rest) (gmove d w gl gr).1 [] clk e bad [w] [d] [])
      (U x (gmove d w gl gr).2 (d :: true :: rest) (gmove d w gl gr).1 [] clk e bad [w] [] []) 3 :=
    (mv1_cons (by decide) rfl).to rfl (Nat.le_refl _)
  have c5 : ExecB (mv1 9 2)
      (U x (gmove d w gl gr).2 (d :: true :: rest) (gmove d w gl gr).1 [] clk e bad [w] [] [])
      (U x (gmove d w gl gr).2 (w :: d :: true :: rest) (gmove d w gl gr).1 [] clk e bad [] [] []) 3 :=
    (mv1_cons (by decide) rfl).to rfl (Nat.le_refl _)
  have c6 := rotk_U (x := x) (gr := (gmove d w gl gr).2) (gl := (gmove d w gl gr).1) (k := [])
    (clk := clk) (e := e) (bad := bad) (fw := []) (fd := []) (ans := []) hm
  have c7 := rot_U (x := x) (gr := (gmove d w gl gr).2) (gl := (gmove d w gl gr).1)
    (k := List.replicate (entryOnes (w :: d :: true :: rest)) true ++ []) (clk := clk) (e := e)
    (bad := bad) (fw := []) (fd := []) (ans := []) (mem_rot hm)
  have c8 := rl_U (x := x) (gr := (gmove d w gl gr).2) (gl := (gmove d w gl gr).1) (clk := clk)
    (e := e) (bad := bad) (fw := []) (fd := []) (ans := []) (entryOnes (w :: d :: true :: rest))
    (rot (rot (w :: d :: true :: rest))) (mem_rot (mem_rot hm))
  refine (a1.seq (a2.seq (a3.seq (ExecB.cs (by exact c1.seq (c2.seq (c3.seq (c4.seq (c5.seq
    (c6.seq (c7.seq c8))))))))))).to rfl ?_
  simp only [length_rot, hn]
  have hq : (R.length + 3) * (8 * R.length + 8) + 1 ≤ rB R.length := by unfold rB; omega
  have he : entryOnes (w :: d :: true :: rest) ≤ R.length := by
    rw [← hn]; exact onesFrom_le _ _ _
  have hm2 := Nat.mul_le_mul_right (rB R.length + 2) he
  have hx := Nat.add_mul R.length 4 (rB R.length + 2)
  unfold stepB
  omega

/-! ## The main loop -/

theorem main_bound (X Y T : Nat) (h : X ≤ Y) :
    1 + X + (T * (X + 2) + 1) + 1 ≤ (T + 1) * (Y + 2) + 1 := by
  have h1 := Nat.mul_le_mul_left T (show X + 2 ≤ Y + 2 by omega)
  have h2 := Nat.add_mul T 1 (Y + 2)
  rw [Nat.one_mul] at h2
  omega

theorem main_U (x e bad : List Bool) : ∀ (T : Nat) (R gl gr : List Bool), false ∈ R →
    ∃ gl' gr' R', ExecB MAIN (U x gr R gl [] (List.replicate T true) e bad [] [] [])
      (U x gr' R' gl' [] [] e bad [] [] (ansOf (runAux T R (ztape gl gr) gl.length)))
      (T * (stepB R.length T + 2) + 1)
  | 0, R, gl, gr, _ => ⟨gl, gr, R, ExecB.to (ExecB.whF (by rfl)) rfl (by omega)⟩
  | T + 1, R, gl, gr, h0 => by
    have hmono : stepB R.length T ≤ stepB R.length (T + 1) := by unfold stepB; omega
    have b1 : ExecB (.pop 6) (U x gr R gl [] (List.replicate (T + 1) true) e bad [] [] [])
        (U x gr R gl [] (List.replicate T true) e bad [] [] []) 1 := ExecB.pop.to rfl (Nat.le_refl _)
    rw [runAux_succ, ztape_head]
    generalize hR1 : rotN (iota gr.head?) R = R1
    cases h2 : R1.getD 2 false with
    | false =>
      rw [if_neg (by decide)]
      have b2 := step_halt (x := x) (e := e) (bad := bad) (gl := gl) (clk := List.replicate T true)
        h0 hR1 h2
      rw [List.length_replicate] at b2
      refine ⟨gl, gr, R1, (ExecB.whT (i := 6) (me := false) (mf := true) (mt := true) (by rfl)
        (b1.seq b2) (ExecB.whF (by rfl))).to rfl ?_⟩
      have := main_bound (stepB R.length T) (stepB R.length (T + 1)) T hmono
      omega
    | true =>
      rw [if_pos rfl]
      obtain ⟨w, d, rest, rfl⟩ : ∃ w d rest, R1 = w :: d :: true :: rest := by
        match R1, h2 with
        | w :: d :: true :: rest, _ => exact ⟨w, d, rest, rfl⟩
        | [], h => simp at h
        | [_], h => simp at h
        | [_, _], h => simp at h
        | _ :: _ :: false :: _, h => simp at h
      have b2 := step_cont (x := x) (e := e) (bad := bad) (gl := gl) (clk := List.replicate T true)
        h0 hR1
      rw [List.length_replicate] at b2
      have hR2 : false ∈ rotN (entryOnes (w :: d :: true :: rest) + 1) (rot (w :: d :: true :: rest)) :=
        mem_rotN _ (mem_rot (by rw [← hR1]; exact mem_rotN _ h0))
      have hn2 : (rotN (entryOnes (w :: d :: true :: rest) + 1) (rot (w :: d :: true :: rest))).length =
          R.length := by rw [length_rotN, length_rot, ← hR1, length_rotN]
      obtain ⟨gl', gr', R', hm⟩ := main_U x e bad T _ (gmove d w gl gr).1 (gmove d w gl gr).2 hR2
      rw [(gmove_ok d w gl gr).1, (gmove_ok d w gl gr).2, hn2] at hm
      refine ⟨gl', gr', R', (ExecB.whT (by rfl) (b1.seq b2) hm).to ?_ ?_⟩
      · rfl
      · exact main_bound _ _ T hmono

/-! ## Setup, length check, and the answer -/

def mvx (b : Bool) : Cmd := .seq (.pop 0) (.seq (.push 2 b) (.seq (.push 6 true) (.push 7 true)))
def MVX : Cmd := .wh 0 false true true (.cs 0 .skip (mvx false) (mvx true))
def CHK : Cmd := .cs 7 (.push 8 true) (.pop 7) (.pop 7)
def lcb (b : Bool) : Cmd := .seq (.pop 1) (.seq (.push 3 b) CHK)
def LC : Cmd := .wh 1 false true true (.cs 1 .skip (lcb false) (lcb true))
def CK : Cmd := .cs 7 .skip (.push 8 true) (.push 8 true)
def FIN : Cmd := .cs 8 (.cs 11 .skip .skip (.push 0 true)) .skip .skip

def UG : Cmd :=
  .seq (.push 2 false) (.seq MVX (.seq (.push 6 true) (.seq (.push 7 true) (.seq ROT
    (.seq LC (.seq (mv 3 1) (.seq CK (.seq MAIN FIN))))))))

theorem mvx_U {c gl k bad fw fd ans : List Bool} : ∀ (s r clk e : List Bool),
    ExecB MVX (U s c r gl k clk e bad fw fd ans)
      (U [] c (s.reverse ++ r) gl k (List.replicate s.length true ++ clk)
        (List.replicate s.length true ++ e) bad fw fd ans) (6 * s.length + 1)
  | [], r, clk, e => ExecB.to (ExecB.whF (by rfl)) rfl (by omega)
  | b :: s, r, clk, e => by
    have hb : ExecB (mvx b) (U (b :: s) c r gl k clk e bad fw fd ans)
        (U s c (b :: r) gl k (true :: clk) (true :: e) bad fw fd ans) 4 :=
      (ExecB.pop.seq (ExecB.push.seq (ExecB.push.seq ExecB.push))).to rfl (Nat.le_refl _)
    have hb' : ExecB (sel (b :: s) .skip (mvx false) (mvx true)) (U (b :: s) c r gl k clk e bad fw fd ans)
        (U s c (b :: r) gl k (true :: clk) (true :: e) bad fw fd ans) 4 := by
      cases b <;> exact hb
    have ih := mvx_U (c := c) (gl := gl) (k := k) (bad := bad) (fw := fw) (fd := fd) (ans := ans)
      s (b :: r) (true :: clk) (true :: e)
    refine (ExecB.whT (by cases b <;> rfl) (ExecB.cs (by exact hb')) ih).to ?_ (by simp only [List.length_cons]; omega)
    simp [U, List.replicate_succ']

theorem lc_U {x r gl k clk ans : List Bool} : ∀ (c tt bd : List Bool) (a : Nat),
    ExecB LC [x, c, r, tt, gl, k, clk, List.replicate a true, bd, [], [], ans, []]
      [x, [], r, c.reverse ++ tt, gl, k, clk, List.replicate (a - c.length) true,
        List.replicate (c.length - a) true ++ bd, [], [], ans, []] (6 * c.length + 1)
  | [], tt, bd, a => ExecB.to (ExecB.whF (by rfl)) (by simp) (by omega)
  | b :: c, tt, bd, 0 => by
    have hb : ExecB (lcb b) [x, b :: c, r, tt, gl, k, clk, List.replicate 0 true, bd, [], [], ans, []]
        [x, c, r, b :: tt, gl, k, clk, [], true :: bd, [], [], ans, []] 4 :=
      (ExecB.pop.seq (ExecB.push.seq (ExecB.cs (by exact ExecB.push)))).to rfl (Nat.le_refl _)
    have hb' : ExecB (sel (b :: c) .skip (lcb false) (lcb true))
        [x, b :: c, r, tt, gl, k, clk, List.replicate 0 true, bd, [], [], ans, []]
        [x, c, r, b :: tt, gl, k, clk, [], true :: bd, [], [], ans, []] 4 := by
      cases b <;> exact hb
    have ih := lc_U (x := x) (r := r) (gl := gl) (k := k) (clk := clk) (ans := ans) c (b :: tt)
      (true :: bd) 0
    refine (ExecB.whT (by cases b <;> rfl) (ExecB.cs (by exact hb')) ih).to ?_ (by simp only [List.length_cons]; omega)
    simp [List.replicate_succ']
  | b :: c, tt, bd, a + 1 => by
    have hb : ExecB (lcb b) [x, b :: c, r, tt, gl, k, clk, List.replicate (a + 1) true, bd, [], [], ans, []]
        [x, c, r, b :: tt, gl, k, clk, List.replicate a true, bd, [], [], ans, []] 4 :=
      (ExecB.pop.seq (ExecB.push.seq (ExecB.cs (by exact ExecB.pop)))).to rfl (Nat.le_refl _)
    have hb' : ExecB (sel (b :: c) .skip (lcb false) (lcb true))
        [x, b :: c, r, tt, gl, k, clk, List.replicate (a + 1) true, bd, [], [], ans, []]
        [x, c, r, b :: tt, gl, k, clk, List.replicate a true, bd, [], [], ans, []] 4 := by
      cases b <;> exact hb
    have ih := lc_U (x := x) (r := r) (gl := gl) (k := k) (clk := clk) (ans := ans) c (b :: tt) bd a
    refine (ExecB.whT (by cases b <;> rfl) (ExecB.cs (by exact hb')) ih).to ?_ (by simp only [List.length_cons]; omega)
    simp

theorem ck_U {x gr r gl clk bad : List Bool} (m : Nat) :
    ExecB CK (U x gr r gl [] clk (List.replicate m true) bad [] [] [])
      (U x gr r gl [] clk (List.replicate m true) (if m = 0 then bad else true :: bad) [] [] []) 2 := by
  cases m with
  | zero => exact ExecB.cs ExecB.skip
  | succ m => exact ExecB.cs (ExecB.push.to rfl (Nat.le_refl _))

theorem fin_U {gr r gl e bad : List Bool} (v : Bool) :
    ∃ S', ExecB FIN (U [] gr r gl [] [] e bad [] [] (ansOf v)) S' 3 ∧
      (S'.getD 0 [] ≠ [] ↔ bad = [] ∧ v = true) := by
  match bad, v with
  | [], false =>
    exact ⟨U [] gr r gl [] [] e [] [] [] [],
      ExecB.to (ExecB.cs (by exact ExecB.cs (by exact ExecB.skip))) rfl (by omega), by simp [U]⟩
  | [], true =>
    exact ⟨U [true] gr r gl [] [] e [] [] [] [true],
      ExecB.to (ExecB.cs (by exact ExecB.cs (by exact ExecB.push))) rfl (by omega), by simp [U]⟩
  | false :: l, v =>
    exact ⟨U [] gr r gl [] [] e (false :: l) [] [] (ansOf v),
      ExecB.to (ExecB.cs (by exact ExecB.skip)) rfl (by omega), by simp [U]⟩
  | true :: l, v =>
    exact ⟨U [] gr r gl [] [] e (true :: l) [] [] (ansOf v),
      ExecB.to (ExecB.cs (by exact ExecB.skip)) rfl (by omega), by simp [U]⟩

/-- Operation bound for `UG` on `s, c`. -/
def ugB (n m : Nat) : Nat :=
  1 + (6 * n + 1 + (1 + (1 + (rB (n + 1) + (6 * m + 1 + (4 * m + 1 + (2 +
    ((n + 1) * (stepB (n + 1) (n + 1) + 2) + 1 + 3))))))))

theorem ug_ok (s c : List Bool) :
    ∃ S', ExecB UG (U s c [] [] [] [] [] [] [] [] []) S' (ugB s.length c.length) ∧
      S'.length = 13 ∧
      (S'.getD 0 [] ≠ [] ↔ c.length = s.length + 1 ∧ run s c (s.length + 1) = true) := by
  have t1 : ExecB (.push 2 false) (U s c [] [] [] [] [] [] [] [] [])
      (U s c [false] [] [] [] [] [] [] [] []) 1 := ExecB.push.to rfl (Nat.le_refl _)
  have t2 := mvx_U (c := c) (gl := []) (k := []) (bad := []) (fw := []) (fd := []) (ans := [])
    s [false] [] []
  simp only [List.append_nil] at t2
  have t3 : ExecB (.push 6 true)
      (U [] c (s.reverse ++ [false]) [] [] (List.replicate s.length true)
        (List.replicate s.length true) [] [] [] [])
      (U [] c (s.reverse ++ [false]) [] [] (List.replicate (s.length + 1) true)
        (List.replicate s.length true) [] [] [] []) 1 := ExecB.push.to rfl (Nat.le_refl _)
  have t4 : ExecB (.push 7 true)
      (U [] c (s.reverse ++ [false]) [] [] (List.replicate (s.length + 1) true)
        (List.replicate s.length true) [] [] [] [])
      (U [] c (s.reverse ++ [false]) [] [] (List.replicate (s.length + 1) true)
        (List.replicate (s.length + 1) true) [] [] [] []) 1 := ExecB.push.to rfl (Nat.le_refl _)
  have h0 : false ∈ s.reverse ++ [false] := by simp
  have t5 := rot_U (x := []) (gr := c) (gl := []) (k := []) (clk := List.replicate (s.length + 1) true)
    (e := List.replicate (s.length + 1) true) (bad := []) (fw := []) (fd := []) (ans := []) h0
  have t6 := lc_U (x := []) (r := rot (s.reverse ++ [false])) (gl := []) (k := [])
    (clk := List.replicate (s.length + 1) true) (ans := []) c [] [] (s.length + 1)
  have t7 := mv_ok (i := 3) (j := 1) (by decide) (c.reverse ++ [])
    [[], [], rot (s.reverse ++ [false]), c.reverse ++ [], [], [], List.replicate (s.length + 1) true,
      List.replicate (s.length + 1 - c.length) true,
      List.replicate (c.length - (s.length + 1)) true ++ [], [], [], [], []]
    (by simp) (by simp) rfl
  have t7' : ExecB (mv 3 1)
      [[], [], rot (s.reverse ++ [false]), c.reverse ++ [], [], [], List.replicate (s.length + 1) true,
        List.replicate (s.length + 1 - c.length) true,
        List.replicate (c.length - (s.length + 1)) true ++ [], [], [], [], []]
      (U [] c (rot (s.reverse ++ [false])) [] [] (List.replicate (s.length + 1) true)
        (List.replicate (s.length + 1 - c.length) true)
        (List.replicate (c.length - (s.length + 1)) true) [] [] [])
      (4 * c.length + 1) := t7.to (by simp [U]) (by simp)
  have t8 := ck_U (x := []) (gr := c) (r := rot (s.reverse ++ [false])) (gl := [])
    (clk := List.replicate (s.length + 1) true) (bad := List.replicate (c.length - (s.length + 1)) true)
    (s.length + 1 - c.length)
  have hR : false ∈ rot (s.reverse ++ [false]) := mem_rot h0
  obtain ⟨gl', gr', R', t9⟩ := main_U []
    (List.replicate (s.length + 1 - c.length) true)
    (if s.length + 1 - c.length = 0 then List.replicate (c.length - (s.length + 1)) true
      else true :: List.replicate (c.length - (s.length + 1)) true)
    (s.length + 1) _ [] c hR
  obtain ⟨S', t10, hS'⟩ := fin_U (gr := gr') (r := R') (gl := gl')
    (e := List.replicate (s.length + 1 - c.length) true)
    (bad := if s.length + 1 - c.length = 0 then List.replicate (c.length - (s.length + 1)) true
      else true :: List.replicate (c.length - (s.length + 1)) true)
    (runAux (s.length + 1) (rot (s.reverse ++ [false])) (ztape [] c) ([] : List Bool).length)
  have hl0 : (s.reverse ++ [false]).length = s.length + 1 := by simp
  have hl : (rot (s.reverse ++ [false])).length = s.length + 1 := by rw [length_rot, hl0]
  rw [hl0] at t5
  rw [hl] at t9
  have hlen : S'.length = 13 := by
    obtain ⟨t, -, ht⟩ := t10
    rw [ht.len]; rfl
  refine ⟨S', (t1.seq (t2.seq (t3.seq (t4.seq (t5.seq (t6.seq (t7'.seq (t8.seq (t9.seq
    t10))))))))).to rfl ?_, hlen, ?_⟩
  · unfold ugB; omega
  · rw [hS']
    have hrun : runAux (s.length + 1) (rot (s.reverse ++ [false])) (ztape [] c) ([] : List Bool).length =
        run s c (s.length + 1) := rfl
    rw [hrun]
    constructor
    · rintro ⟨hb, hv⟩
      refine ⟨?_, hv⟩
      by_cases h1 : s.length + 1 - c.length = 0
      · rw [if_pos h1] at hb
        have : c.length - (s.length + 1) = 0 := by
          cases h : c.length - (s.length + 1) with
          | zero => rfl
          | succ q => rw [h] at hb; simp at hb
        omega
      · rw [if_neg h1] at hb; simp at hb
    · rintro ⟨hc, hv⟩
      refine ⟨?_, hv⟩
      rw [if_pos (by omega), show c.length - (s.length + 1) = 0 by omega]
      rfl

end ZP.Cx
