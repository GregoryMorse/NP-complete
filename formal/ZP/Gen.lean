module

public import ZP.Ents

@[expose] public section

/-!
# Writing out compiled entries

Stack programs over eight stacks that push the bits of compiled entries on stack 1.
During this phase stack 2 holds `NN` ones and stack 4 holds `P` ones (`ES`). An entry
`w d 1^K 0` is pushed bit by bit; `K` is a constant, `NN` minus a constant (copy
stack 2, then pop), or `P + 7`.

`Em N P c es B`: from any `ES X O N P`, `c` pushes the bits of `flat es` within `B`
steps. `em_genRows`: the static rows of a machine are written by `genRows`.
-/

namespace ZP.Cx

/-! ## Generic loops -/

theorem rep_snoc (b : Bool) : ∀ (n : Nat) (X : List Bool),
    List.replicate n b ++ b :: X = List.replicate (n + 1) b ++ X
  | 0, _ => rfl
  | n + 1, X => by
    rw [List.replicate_succ, List.cons_append, rep_snoc b n X]
    rfl

def pushB (i : Nat) (b : Bool) : Nat → Cmd
  | 0 => .skip
  | n + 1 => .seq (.push i b) (pushB i b n)

theorem pushB_gen {i : Nat} (b : Bool) : ∀ (n : Nat) (S : List (List Bool)), i < S.length →
    ExecB (pushB i b n) S (S.set i (List.replicate n b ++ S.getD i [])) (n + 1)
  | 0, S, hi => ExecB.skip.to (by stk_eq) (Nat.le_refl _)
  | n + 1, S, hi => by
    have h2 := pushB_gen b n (S.set i (b :: S.getD i [])) (by simpa using hi)
    rw [getD_set_eq _ hi, rep_snoc] at h2
    refine (ExecB.push.seq h2).to (by stk_eq) (by omega)

theorem pushK_gen {i : Nat} : ∀ (n : Nat) (S : List (List Bool)), i < S.length →
    ExecB (pushK i n) S (S.set i (List.replicate n true ++ S.getD i [])) (n + 1)
  | 0, S, hi => ExecB.skip.to (by stk_eq) (Nat.le_refl _)
  | n + 1, S, hi => by
    have h2 := pushK_gen n (S.set i (true :: S.getD i [])) (by simpa using hi)
    rw [getD_set_eq _ hi, rep_snoc] at h2
    refine (ExecB.push.seq h2).to (by stk_eq) (by omega)

def popK (i : Nat) : Nat → Cmd
  | 0 => .skip
  | j + 1 => .seq (.pop i) (popK i j)

theorem popK_gen {i : Nat} : ∀ (j : Nat) (S : List (List Bool)) (u : List Bool), i < S.length →
    S.getD i [] = List.replicate j true ++ u → ExecB (popK i j) S (S.set i u) (j + 1)
  | 0, S, u, hi, h => by
    have h' : S.getD i [] = u := by simpa using h
    exact ExecB.skip.to (by stk_eq) (Nat.le_refl _)
  | j + 1, S, u, hi, h => by
    have h2 := popK_gen j (S.set i (S.getD i []).tail) u (by simpa using hi)
      (by rw [getD_set_eq _ hi, h]; rfl)
    refine (ExecB.pop.seq h2).to (by stk_eq) (by omega)

/-- Move unary stack `i` onto both `j` and `l`. -/
def dup (i j l : Nat) : Cmd := .wh i false true true (.seq (.pop i) (.seq (.push j true) (.push l true)))

theorem dup_ok {i j l : Nat} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    ∀ (a : Nat) (S : List (List Bool)), i < S.length → j < S.length → l < S.length →
      S.getD i [] = List.replicate a true →
      ExecB (dup i j l) S (((S.set i []).set j (List.replicate a true ++ S.getD j [])).set l
        (List.replicate a true ++ S.getD l [])) (4 * a + 1)
  | 0, S, hi, hj, hl, h => by
    have h' : S.getD i [] = [] := h
    refine (ExecB.whF (by rw [h]; rfl)).to ?_ (by omega)
    simp only [List.replicate_zero, List.nil_append]
    stk_eq
  | a + 1, S, hi, hj, hl, h => by
    have h1 : ExecB (.pop i) S (S.set i (List.replicate a true)) 1 :=
      ExecB.pop.to (by rw [h]; rfl) (Nat.le_refl _)
    have h2 : ExecB (.push j true) (S.set i (List.replicate a true))
        ((S.set i (List.replicate a true)).set j (true :: S.getD j [])) 1 :=
      ExecB.push.to (by rw [getD_set_ne _ (Ne.symm hij)]) (Nat.le_refl _)
    have h3 : ExecB (.push l true) ((S.set i (List.replicate a true)).set j (true :: S.getD j []))
        (((S.set i (List.replicate a true)).set j (true :: S.getD j [])).set l
          (true :: S.getD l [])) 1 :=
      ExecB.push.to (by rw [getD_set_ne _ (Ne.symm hjl), getD_set_ne _ (Ne.symm hil)])
        (Nat.le_refl _)
    have h4 := dup_ok hij hil hjl a
      (((S.set i (List.replicate a true)).set j (true :: S.getD j [])).set l (true :: S.getD l []))
      (by simpa using hi) (by simpa using hj) (by simpa using hl)
      (by rw [getD_set_ne _ hil, getD_set_ne _ hij, getD_set_eq _ hi])
    have g1 : (((S.set i (List.replicate a true)).set j (true :: S.getD j [])).set l
        (true :: S.getD l [])).getD j [] = true :: S.getD j [] := by
      rw [getD_set_ne _ hjl, getD_set_eq _ (by simpa using hj)]
    have g2 : (((S.set i (List.replicate a true)).set j (true :: S.getD j [])).set l
        (true :: S.getD l [])).getD l [] = true :: S.getD l [] := by
      rw [getD_set_eq _ (by simpa using hl)]
    rw [g1, g2, rep_snoc, rep_snoc] at h4
    refine (ExecB.whT (by rw [h]; rfl) (h1.seq (h2.seq h3)) h4).to ?_ (by omega)
    stk_eq

/-- Move unary stack `i` onto `j`, `K` ones per one. -/
def addk (i j K : Nat) : Cmd := .wh i false true true (.seq (.pop i) (pushK j K))

theorem addk_ok {i j K : Nat} (hij : i ≠ j) : ∀ (c : Nat) (S : List (List Bool)), i < S.length →
    j < S.length → S.getD i [] = List.replicate c true →
      ExecB (addk i j K) S ((S.set i []).set j (List.replicate (c * K) true ++ S.getD j []))
        (c * (K + 3) + 1)
  | 0, S, hi, hj, h => by
    have h' : S.getD i [] = [] := h
    refine (ExecB.whF (by rw [h]; rfl)).to ?_ (by omega)
    simp only [Nat.zero_mul, List.replicate_zero, List.nil_append]
    stk_eq
  | c + 1, S, hi, hj, h => by
    have h1 : ExecB (.pop i) S (S.set i (List.replicate c true)) 1 :=
      ExecB.pop.to (by rw [h]; rfl) (Nat.le_refl _)
    have h2 := pushK_gen (i := j) K (S.set i (List.replicate c true)) (by simpa using hj)
    rw [getD_set_ne _ (Ne.symm hij)] at h2
    have h3 := addk_ok (K := K) hij c ((S.set i (List.replicate c true)).set j
      (List.replicate K true ++ S.getD j [])) (by simpa using hi) (by simpa using hj)
      (by rw [getD_set_ne _ hij, getD_set_eq _ hi])
    rw [getD_set_eq _ (by simpa using hj), ← List.append_assoc, ← rep_add,
      show c * K + K = (c + 1) * K by rw [Nat.add_mul, Nat.one_mul]] at h3
    refine (ExecB.whT (by rw [h]; rfl) (h1.seq h2) h3).to ?_
      (by rw [Nat.add_mul, Nat.one_mul]; generalize c * (K + 3) = Z; omega)
    stk_eq

/-! ## The emission state -/

def ES (X O : List Bool) (N P : Nat) : List (List Bool) :=
  WS X O (List.replicate N true) [] (List.replicate P true) [] [] []

def Em (N P : Nat) (c : Cmd) (es : List Ent) (B : Nat) : Prop :=
  ∀ X O, ExecB c (ES X O N P) (ES X ((flat es).reverse ++ O) N P) B

section em
variable {N P : Nat}

theorem Em.seq {c1 c2 : Cmd} {e1 e2 : List Ent} {B1 B2 : Nat} (h1 : Em N P c1 e1 B1)
    (h2 : Em N P c2 e2 B2) : Em N P (.seq c1 c2) (e1 ++ e2) (B1 + B2) := fun X O =>
  ((h1 X O).seq (h2 X _)).to (by rw [flat_app, List.reverse_append, List.append_assoc])
    (Nat.le_refl _)

theorem Em.cast {c : Cmd} {e e' : List Ent} {B B' : Nat} (h : Em N P c e B) (he : e = e')
    (hB : B ≤ B') : Em N P c e' B' := fun X O => (h X O).to (by rw [he]) hB

theorem flat1 (e : Ent) (O : List Bool) :
    (flat [e]).reverse ++ O = false :: (List.replicate e.k true ++ e.d :: e.w :: O) := by
  simp [flat, ebits, List.reverse_replicate]

/-- Push `w`, `d`, run `body` (which pushes `K` ones), push `0`. -/
def eW (w d : Bool) (body : Cmd) : Cmd := .seq (.push 1 w) (.seq (.push 1 d) (.seq body (.push 1 false)))

theorem em_eW {w d : Bool} {body : Cmd} {K Bb : Nat}
    (hb : ∀ X O, ExecB body (ES X O N P) (ES X (List.replicate K true ++ O) N P) Bb) :
    Em N P (eW w d body) [⟨w, d, K⟩] (Bb + 3) := fun X O => by
  have e1 : ExecB (.push 1 w) (ES X O N P) (ES X (w :: O) N P) 1 := ExecB.push.to rfl (Nat.le_refl _)
  have e2 : ExecB (.push 1 d) (ES X (w :: O) N P) (ES X (d :: w :: O) N P) 1 :=
    ExecB.push.to rfl (Nat.le_refl _)
  have e4 : ExecB (.push 1 false) (ES X (List.replicate K true ++ d :: w :: O) N P)
      (ES X (false :: (List.replicate K true ++ d :: w :: O)) N P) 1 :=
    ExecB.push.to rfl (Nat.le_refl _)
  refine (e1.seq (e2.seq ((hb X _).seq e4))).to ?_ (by omega)
  rw [flat1]

theorem body_skip : ∀ X O, ExecB .skip (ES X O N P) (ES X (List.replicate 0 true ++ O) N P) 1 :=
  fun _ _ => ExecB.skip

theorem body_pushK (K : Nat) :
    ∀ X O, ExecB (pushK 1 K) (ES X O N P) (ES X (List.replicate K true ++ O) N P) (K + 1) :=
  fun X O => (pushK_gen K (ES X O N P) (by simp [ES, WS])).to rfl (Nat.le_refl _)

/-- Copy stack 2 (`N` ones) onto stack 1. -/
def NNc : Cmd := .seq (dup 2 1 6) (mv 6 2)

theorem body_NNc : ∀ X O, ExecB NNc (ES X O N P) (ES X (List.replicate N true ++ O) N P)
    (8 * N + 2) := fun X O => by
  have e1 := dup_ok (i := 2) (j := 1) (l := 6) (by decide) (by decide) (by decide) N (ES X O N P)
    (by simp [ES, WS]) (by simp [ES, WS]) (by simp [ES, WS]) rfl
  have e1' : ExecB (dup 2 1 6) (ES X O N P)
      (WS X (List.replicate N true ++ O) [] [] (List.replicate P true) [] (List.replicate N true) [])
      (4 * N + 1) := e1.to (by first | rfl | simp [ES, WS]) (Nat.le_refl _)
  have e2 := mv_ok (i := 6) (j := 2) (by decide) (List.replicate N true)
    (WS X (List.replicate N true ++ O) [] [] (List.replicate P true) [] (List.replicate N true) [])
    (by simp [WS]) (by simp [WS]) rfl
  refine (e1'.seq e2).to ?_ (by simp only [List.length_replicate]; omega)
  simp [ES, WS, List.reverse_replicate]

/-- Copy stack 4 (`P` ones) onto stack 1. -/
def PADc : Cmd := .seq (dup 4 1 6) (mv 6 4)

theorem body_PADc : ∀ X O, ExecB PADc (ES X O N P) (ES X (List.replicate P true ++ O) N P)
    (8 * P + 2) := fun X O => by
  have e1 := dup_ok (i := 4) (j := 1) (l := 6) (by decide) (by decide) (by decide) P (ES X O N P)
    (by simp [ES, WS]) (by simp [ES, WS]) (by simp [ES, WS]) rfl
  have e1' : ExecB (dup 4 1 6) (ES X O N P)
      (WS X (List.replicate P true ++ O) (List.replicate N true) [] [] [] (List.replicate P true) [])
      (4 * P + 1) := e1.to (by first | rfl | simp [ES, WS]) (Nat.le_refl _)
  have e2 := mv_ok (i := 6) (j := 4) (by decide) (List.replicate P true)
    (WS X (List.replicate P true ++ O) (List.replicate N true) [] [] [] (List.replicate P true) [])
    (by simp [WS]) (by simp [WS]) rfl
  refine (e1'.seq e2).to ?_ (by simp only [List.length_replicate]; omega)
  simp [ES, WS, List.reverse_replicate]

theorem body_NNpop {j : Nat} (hj : j ≤ N) : ∀ X O, ExecB (.seq NNc (popK 1 j)) (ES X O N P)
    (ES X (List.replicate (N - j) true ++ O) N P) (9 * N + 3) := fun X O => by
  have e2 := popK_gen (i := 1) j (ES X (List.replicate N true ++ O) N P)
    (List.replicate (N - j) true ++ O) (by simp [ES, WS])
    (by
      show List.replicate N true ++ O = _
      rw [← List.append_assoc, ← rep_add, show j + (N - j) = N by omega])
  exact ((body_NNc X O).seq e2).to rfl (by omega)

theorem body_PAD7 : ∀ X O, ExecB (.seq PADc (pushK 1 7)) (ES X O N P)
    (ES X (List.replicate (P + 7) true ++ O) N P) (8 * P + 10) := fun X O => by
  refine ((body_PADc X O).seq (body_pushK 7 X _)).to ?_ (by omega)
  rw [← List.append_assoc, ← rep_add, Nat.add_comm 7 P]

end em

/-! ## Static rows -/

def genE (p : Nat) : Act → Cmd
  | .halt b => eW b false .skip
  | .go w r q => eW w r (if p + 3 ≤ 3 * q then pushK 1 (3 * q - p - 2)
      else .seq NNc (popK 1 (p + 2 - 3 * q)))

theorem em_genE {N P B p : Nat} (a : Act) (hp : p + 3 ≤ N) (ht : tgA B a) (hB : 3 * B ≤ N) :
    Em N P (genE p a) [entG N p a] (9 * N + 7) := by
  cases a with
  | halt b => exact (em_eW body_skip).cast rfl (by omega)
  | go w r q =>
    have hq : q ≤ B := ht
    by_cases hc : p + 3 ≤ 3 * q
    · have h := em_eW (w := w) (d := r) (body_pushK (N := N) (P := P) (3 * q - p - 2))
      have h' : Em N P (genE p (.go w r q)) [⟨w, r, 3 * q - p - 2⟩] (3 * q - p - 2 + 1 + 3) := by
        unfold genE; rw [if_pos hc]; exact h
      exact h'.cast (by unfold entG; rw [if_pos hc]) (by omega)
    · have h := em_eW (w := w) (d := r) (body_NNpop (N := N) (P := P) (j := p + 2 - 3 * q)
        (by omega))
      have h' : Em N P (genE p (.go w r q)) [⟨w, r, N - (p + 2 - 3 * q)⟩] (9 * N + 3 + 3) := by
        unfold genE; rw [if_neg hc]; exact h
      refine h'.cast ?_ (by omega)
      unfold entG; rw [if_neg hc]
      congr 2
      omega

def genRows : Nat → List (Act × Act × Act) → Cmd
  | _, [] => .skip
  | q, r :: rs => .seq (genE (3 * q) r.1) (.seq (genE (3 * q + 1) r.2.1)
      (.seq (genE (3 * q + 2) r.2.2) (genRows (q + 1) rs)))

theorem em_genRows {N P B : Nat} (hB : 3 * B ≤ N) : ∀ (rows : List (Act × Act × Act)) (q : Nat),
    TgLe B rows → 3 * (q + rows.length) + 3 ≤ N →
    Em N P (genRows q rows) (rowsG N q rows) (rows.length * (27 * N + 21) + 1)
  | [], q, _, _ => fun X O => ExecB.skip.to rfl (by simp)
  | r :: rs, q, ht, hl => by
    simp only [List.length_cons] at hl
    obtain ⟨⟨t1, t2, t3⟩, ht'⟩ := ht
    have h1 := em_genE (P := P) r.1 (p := 3 * q) (by omega) t1 hB
    have h2 := em_genE (P := P) r.2.1 (p := 3 * q + 1) (by omega) t2 hB
    have h3 := em_genE (P := P) r.2.2 (p := 3 * q + 2) (by omega) t3 hB
    have h4 := em_genRows (P := P) hB rs (q + 1) ht' (by omega)
    refine (h1.seq (h2.seq (h3.seq h4))).cast rfl ?_
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    generalize rs.length * (27 * N + 21) = Z
    omega

theorem ok_popK : ∀ j, Ok 8 (popK 1 j)
  | 0 => trivial
  | j + 1 => ⟨show 1 < 8 by decide, ok_popK j⟩

theorem ok_genE (p : Nat) : ∀ a, Ok 8 (genE p a)
  | .halt b => by cases b <;> exact okb_ok 8 (eW _ false .skip) (by decide)
  | .go w r q => by
    have hb : Ok 8 (if p + 3 ≤ 3 * q then pushK 1 (3 * q - p - 2)
        else .seq NNc (popK 1 (p + 2 - 3 * q))) := by
      split
      · exact ok_pushK (by decide) _
      · exact ⟨okb_ok 8 NNc (by decide), ok_popK _⟩
    exact ⟨show 1 < 8 by decide, show 1 < 8 by decide, hb, show 1 < 8 by decide⟩

theorem ok_genRows : ∀ (rows : List (Act × Act × Act)) (q : Nat), Ok 8 (genRows q rows)
  | [], _ => trivial
  | r :: rs, q => ⟨ok_genE _ _, ok_genE _ _, ok_genE _ _, ok_genRows rs (q + 1)⟩

end ZP.Cx
