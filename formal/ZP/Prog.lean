module

public import ZP.Pop

@[expose] public section

/-!
# A stack language and its compiler

Programs `Cmd` act on `k` stacks of bits: push, pop, a three-way branch on the top of
a stack (empty, 0, 1), sequencing and a while loop on the top. `Exec c S S' t`: from
stacks `S`, `c` ends with `S'` after `t` operations. `frag k c s e` compiles `c` to
rows starting at state `s` with exit `e`; `frag_ok`: the rows lead from `lay S` to
`lay S'` (junk after the layout may change) in at most `40 * t * W` steps, where `W`
bounds the layout size during the run.
-/

namespace ZP.Cx

inductive Cmd where
  | push (i : Nat) (b : Bool)
  | pop (i : Nat)
  | cs (i : Nat) (pe pf pt : Cmd)
  | seq (p q : Cmd)
  | wh (i : Nat) (me mf mt : Bool) (p : Cmd)
  | skip

def sel {α : Type} : List Bool → α → α → α → α
  | [], a, _, _ => a
  | false :: _, _, b, _ => b
  | true :: _, _, _, c => c

inductive Exec : Cmd → List (List Bool) → List (List Bool) → Nat → Prop
  | push {i : Nat} {b : Bool} {S : List (List Bool)} :
      Exec (.push i b) S (S.set i (b :: S.getD i [])) 1
  | pop {i : Nat} {S : List (List Bool)} : Exec (.pop i) S (S.set i (S.getD i []).tail) 1
  | cs {i : Nat} {pe pf pt : Cmd} {S S' : List (List Bool)} {t : Nat} :
      Exec (sel (S.getD i []) pe pf pt) S S' t → Exec (.cs i pe pf pt) S S' (t + 1)
  | seq {p q : Cmd} {S S1 S2 : List (List Bool)} {t1 t2 : Nat} :
      Exec p S S1 t1 → Exec q S1 S2 t2 → Exec (.seq p q) S S2 (t1 + t2)
  | whT {i : Nat} {me mf mt : Bool} {p : Cmd} {S S1 S2 : List (List Bool)} {t1 t2 : Nat} :
      sel (S.getD i []) me mf mt = true → Exec p S S1 t1 → Exec (.wh i me mf mt p) S1 S2 t2 →
      Exec (.wh i me mf mt p) S S2 (t1 + t2 + 1)
  | whF {i : Nat} {me mf mt : Bool} {p : Cmd} {S : List (List Bool)} :
      sel (S.getD i []) me mf mt = false → Exec (.wh i me mf mt p) S S 1
  | skip {S : List (List Bool)} : Exec .skip S S 1

/-- All stack indices are below `k`. -/
def Ok (k : Nat) : Cmd → Prop
  | .push i _ => i < k
  | .pop i => i < k
  | .cs i a b c => i < k ∧ Ok k a ∧ Ok k b ∧ Ok k c
  | .seq p q => Ok k p ∧ Ok k q
  | .wh i _ _ _ p => i < k ∧ Ok k p
  | .skip => True

def flen (k : Nat) : Cmd → Nat
  | .push i _ => 3 * i + 2 + (8 * (k - i) + 24)
  | .pop i => 3 * i + 2 + (21 * (k - i - 1) + 63)
  | .cs i a b c => 3 * i + 2 + 63 + flen k a + flen k b + flen k c
  | .seq p q => flen k p + flen k q
  | .wh i _ _ _ p => 3 * i + 2 + 63 + flen k p
  | .skip => 2

def frag (k : Nat) : Cmd → Nat → Nat → List (Act × Act × Act)
  | .push i b, s, e => preRows s i (p0 (s + 3 * i + 2) true b) ++ pushRows (s + 3 * i + 2) e (k - i)
  | .pop i, s, e => preRows s i (s + 3 * i + 2) ++ popRows (s + 3 * i + 2) e (k - i - 1)
  | .cs i a b c, s, e =>
    preRows s i (s + 3 * i + 2) ++
      testRows (s + 3 * i + 2) (s + 3 * i + 65) (s + 3 * i + 65 + flen k a)
        (s + 3 * i + 65 + flen k a + flen k b) ++
      frag k a (s + 3 * i + 65) e ++ frag k b (s + 3 * i + 65 + flen k a) e ++
      frag k c (s + 3 * i + 65 + flen k a + flen k b) e
  | .seq p q, s, e => frag k p s (s + flen k p) ++ frag k q (s + flen k p) e
  | .wh i me mf mt p, s, e =>
    preRows s i (s + 3 * i + 2) ++
      testRows (s + 3 * i + 2) (if me then s + 3 * i + 65 else e)
        (if mf then s + 3 * i + 65 else e) (if mt then s + 3 * i + 65 else e) ++
      frag k p (s + 3 * i + 65) s
  | .skip, s, e => tramp s e

/-! ## Lengths -/

theorem length_retRows (s e : Nat) : (retRows s e).length = 20 := rfl

theorem length_testRows (s a b c : Nat) : (testRows s a b c).length = 63 := rfl

theorem length_pushRows (e : Nat) : ∀ c s, (pushRows s e c).length = 8 * c + 24
  | 0, _ => rfl
  | c + 1, s => by
    have h1 : (blockRows s (s + 8)).length = 8 := rfl
    show (blockRows s (s + 8) ++ pushRows (s + 8) e c).length = _
    rw [List.length_append, h1, length_pushRows e c (s + 8)]
    omega

theorem length_popBlocks (e : Nat) : ∀ c b, (popBlocks b e c).length = 21 * c + 20
  | 0, _ => rfl
  | c + 1, b => by
    have h1 : (popBlk b (b + 21)).length = 21 := rfl
    show (popBlk b (b + 21) ++ popBlocks (b + 21) e c).length = _
    rw [List.length_append, h1, length_popBlocks e c (b + 21)]
    omega

theorem length_popRows (s e c : Nat) : (popRows s e c).length = 21 * c + 63 := by
  unfold popRows
  rw [List.length_append, List.length_append, length_popBlocks]
  simp only [List.length_cons, List.length_nil, length_retRows]
  omega

theorem length_frag (k : Nat) : ∀ (c : Cmd) (s e : Nat), (frag k c s e).length = flen k c
  | .push i b, s, e => by
    simp only [frag, flen, List.length_append, length_preRows, length_pushRows]
  | .pop i, s, e => by
    simp only [frag, flen, List.length_append, length_preRows, length_popRows]
  | .cs i a b c, s, e => by
    simp only [frag, flen, List.length_append, length_preRows, length_testRows,
      length_frag k a, length_frag k b, length_frag k c]
    omega
  | .seq p q, s, e => by
    simp only [frag, flen, List.length_append, length_frag k p, length_frag k q]
  | .wh i me mf mt p, s, e => by
    simp only [frag, flen, List.length_append, length_preRows, length_testRows, length_frag k p]
    omega
  | .skip, s, e => rfl

/-! ## Lists of stacks -/

theorem drop_get : ∀ (S : List (List Bool)) (i : Nat), i < S.length →
    S.drop i = S.getD i [] :: S.drop (i + 1)
  | [], _, h => absurd h (by simp)
  | x :: S, 0, _ => rfl
  | x :: S, i + 1, h => by
    show S.drop i = S.getD i [] :: S.drop (i + 1)
    exact drop_get S i (by simp at h; omega)

theorem set_split : ∀ (S : List (List Bool)) (i : Nat) (st : List Bool), i < S.length →
    S.set i st = S.take i ++ st :: S.drop (i + 1)
  | [], _, _, h => absurd h (by simp)
  | x :: S, 0, st, _ => rfl
  | x :: S, i + 1, st, h => by
    show x :: S.set i st = x :: (S.take i ++ st :: S.drop (i + 1))
    rw [set_split S i st (by simp at h; omega)]

theorem lay_split (S : List (List Bool)) (i : Nat) (hi : i < S.length) :
    lay S = lay (S.take i) ++ lay (S.getD i [] :: S.drop (i + 1)) := by
  rw [← drop_get S i hi, ← lay_append, List.take_append_drop]

theorem lay_set (S : List (List Bool)) (i : Nat) (hi : i < S.length) (st : List Bool) :
    lay (S.set i st) = lay (S.take i) ++ lay (st :: S.drop (i + 1)) := by
  rw [set_split S i st hi, lay_append]

theorem length_set_lay (S : List (List Bool)) (i : Nat) (st : List Bool) :
    (lay (S.set i st)).length + 2 * (S.getD i []).length ≤ (lay S).length + 2 * st.length := by
  by_cases hi : i < S.length
  · rw [lay_set S i hi, lay_split S i hi]
    simp [length_encR]
    omega
  · have h1 : S.set i st = S := List.set_eq_of_length_le (by omega)
    have h2 : S.getD i [] = [] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : S.length ≤ i)]
    rw [h1, h2]
    simp

theorem Exec.len {c : Cmd} {S S' : List (List Bool)} {t : Nat} (h : Exec c S S' t) :
    S'.length = S.length := by
  induction h with
  | push => simp
  | pop => simp
  | cs _ ih => exact ih
  | seq _ _ ih1 ih2 => rw [ih2, ih1]
  | whT _ _ _ ih1 ih2 => rw [ih2, ih1]
  | whF _ => rfl
  | skip => rfl

theorem Exec.lay_le {c : Cmd} {S S' : List (List Bool)} {t : Nat} (h : Exec c S S' t) :
    (lay S').length ≤ (lay S).length + 2 * t := by
  induction h with
  | @push i b S =>
    have := length_set_lay S i (b :: S.getD i [])
    simp at this
    omega
  | @pop i S =>
    have := length_set_lay S i (S.getD i []).tail
    have h2 : (S.getD i []).tail.length ≤ (S.getD i []).length := by simp
    omega
  | cs _ ih => omega
  | seq _ _ ih1 ih2 => omega
  | whT _ _ _ ih1 ih2 => omega
  | whF _ => omega
  | skip => omega

theorem ok_sel (k : Nat) (a b c : Cmd) (ha : Ok k a) (hb : Ok k b) (hc : Ok k c) :
    ∀ st : List Bool, Ok k (sel st a b c)
  | [] => ha
  | false :: _ => hb
  | true :: _ => hc

theorem sub_sel {M : Mach} {k : Nat} {a b c : Cmd} {e ae af at : Nat}
    (ha : Sub M ae (frag k a ae e)) (hb : Sub M af (frag k b af e)) (hc : Sub M at (frag k c at e)) :
    ∀ st : List Bool, Sub M (tsel ae af at st) (frag k (sel st a b c) (tsel ae af at st) e)
  | [] => ha
  | false :: _ => hb
  | true :: _ => hc

theorem tsel_if (me mf mt : Bool) (b e : Nat) : ∀ st : List Bool,
    tsel (if me then b else e) (if mf then b else e) (if mt then b else e) st =
      if sel st me mf mt then b else e
  | [] => rfl
  | false :: _ => rfl
  | true :: _ => rfl

theorem set_same (S : List (List Bool)) (i : Nat) (h : S.getD i [] = []) : S.set i [] = S := by
  by_cases hi : i < S.length
  · rw [set_split S i [] hi, ← h, ← drop_get S i hi, List.take_append_drop]
  · exact List.set_eq_of_length_le (by omega)

/-! ## The test step, shared by branches and loops -/

theorem test_full {M : Mach} {s i ae af at : Nat} (S : List (List Bool)) (hi : i < S.length)
    (hp : Sub M s (preRows s i (s + 3 * i + 2)))
    (ht : Sub M (s + 3 * i + 2) (testRows (s + 3 * i + 2) ae af at)) (X : List Bool) :
    ∃ T, T ≤ 8 * (lay S).length + 10 ∧
      Lead M s [] (lay S ++ X) (tsel ae af at (S.getD i [])) [] (lay S ++ X) T := by
  have h1 := pre_ok hp S hi X
  rw [drop_get S i hi] at h1
  have h2 := test_ok ht (S.getD i []) (lay (S.take i)).reverse (lay (S.drop (i + 1)) ++ X)
  have hl := lay_split S i hi
  refine ⟨_, ?_, ((h1.re rfl rfl (by simp) rfl).trans h2).re rfl rfl ?_ rfl⟩
  · rw [hl]
    simp [length_encR]
    omega
  · rw [hl]
    simp

/-! ## Correctness of the compiler -/

theorem frag_ok {k : Nat} (hk0 : 0 < k) {c : Cmd} {S S' : List (List Bool)} {t : Nat}
    (h : Exec c S S' t) : S.length = k → Ok k c → ∀ (M : Mach) (s e : Nat),
      Sub M s (frag k c s e) → ∀ (W : Nat) (X : List Bool), (lay S).length + 2 * t + 2 ≤ W →
        ∃ X' T, T ≤ 40 * t * W ∧ Lead M s [] (lay S ++ X) e [] (lay S' ++ X') T := by
  induction h with
  | @push i b S =>
    intro hk hok M s e hs W X hW
    have hi : i < S.length := by rw [hk]; exact hok
    have hs1 : Sub M s (preRows s i (p0 (s + 3 * i + 2) true b)) := hs.left
    have hs2 : Sub M (s + 3 * i + 2) (pushRows (s + 3 * i + 2) e (k - i)) :=
      hs.at (by rw [length_preRows]; omega)
    have hc : k - i = (k - i - 1) + 1 := by omega
    rw [hc] at hs2
    have h1 := pre_ok hs1 S hi X
    rw [drop_get S i hi, lay_layI _ (by simp)] at h1
    have h2 := push_blocks e (k - i - 1) (s + 3 * i + 2) (S.getD i [] :: S.drop (i + 1))
      (by simp; omega) hs2 true b (lay (S.take i)).reverse X
    have hf : ∀ c g, Sub M g (pushRows g e c) → Sub M (g + 8 * c) (finRows (g + 8 * c) e) := by
      intro c
      induction c with
      | zero => intro g hg; exact hg
      | succ c ih =>
        intro g hg
        have := ih (g + 8) (hg.at rfl)
        rwa [show g + 8 + 8 * c = g + 8 * (c + 1) by omega] at this
    have h3 := push_fin (hf _ _ hs2) ((true :: b :: layI (S.getD i [] :: S.drop (i + 1))).reverse ++
      (lay (S.take i)).reverse) X
    have hl := lay_split S i hi
    have hl2 := lay_layI (S.getD i [] :: S.drop (i + 1)) (by simp)
    refine ⟨X.drop 2, _, ?_, ((h1.re rfl rfl (by simp) rfl).trans (h2.trans h3)).re rfl rfl ?_ rfl⟩
    · have hL : (lay S).length = (lay (S.take i)).length +
          (layI (S.getD i [] :: S.drop (i + 1))).length + 2 := by
        rw [hl, hl2]; simp; omega
      simp only [List.length_append, List.length_reverse, List.length_cons]
      omega
    · rw [lay_set S i hi, show lay ((b :: S.getD i []) :: S.drop (i + 1)) =
        true :: b :: lay (S.getD i [] :: S.drop (i + 1)) by simp, hl2]
      simp
  | @pop i S =>
    intro hk hok M s e hs W X hW
    have hi : i < S.length := by rw [hk]; exact hok
    have hs1 : Sub M s (preRows s i (s + 3 * i + 2)) := hs.left
    have hs2 : Sub M (s + 3 * i + 2) (popRows (s + 3 * i + 2) e (k - i - 1)) :=
      hs.at (by rw [length_preRows]; omega)
    have h1 := pre_ok hs1 S hi X
    rw [drop_get S i hi] at h1
    have hl := lay_split S i hi
    cases hst : S.getD i [] with
    | nil =>
      rw [hst] at h1 hl
      have h2 := pop_empty hs2 (lay (S.take i)).reverse (lay (S.drop (i + 1)) ++ X)
      refine ⟨X, _, ?_, ((h1.re rfl rfl (by simp) rfl).trans h2).re rfl rfl ?_ rfl⟩
      · rw [hl]
        simp
        omega
      · rw [List.tail_nil, set_same S i hst, hl]
        simp
    | cons b st =>
      rw [hst] at h1 hl
      obtain ⟨T2, hT2, h2⟩ := pop_full hs2 b st (S.drop (i + 1)) (by simp; omega)
        (lay (S.take i)).reverse X
      refine ⟨false :: true :: X, _, ?_, ((h1.re rfl rfl (by simp) rfl).trans h2).re rfl rfl ?_ rfl⟩
      · have : (lay (st :: S.drop (i + 1))).length ≤ (lay ((b :: st) :: S.drop (i + 1))).length := by
          simp
        rw [hl] at hW
        simp only [List.length_append, List.length_reverse] at hW hT2 ⊢
        omega
      · rw [List.tail_cons, lay_set S i hi]
        simp
  | @cs i pe pf pt S S' t _ ih =>
    intro hk hok M s e hs W X hW
    have hi : i < S.length := by rw [hk]; exact hok.1
    have hp : Sub M s (preRows s i (s + 3 * i + 2)) := hs.left.left.left.left
    have ht : Sub M (s + 3 * i + 2) (testRows (s + 3 * i + 2) (s + 3 * i + 65)
        (s + 3 * i + 65 + flen k pe) (s + 3 * i + 65 + flen k pe + flen k pf)) :=
      hs.left.left.left.at (by rw [length_preRows]; omega)
    have ha : Sub M (s + 3 * i + 65) (frag k pe (s + 3 * i + 65) e) :=
      hs.left.left.at (by rw [List.length_append, length_preRows, length_testRows]; omega)
    have hb : Sub M (s + 3 * i + 65 + flen k pe) (frag k pf (s + 3 * i + 65 + flen k pe) e) :=
      hs.left.at (by
        rw [List.length_append, List.length_append, length_preRows, length_testRows, length_frag]
        omega)
    have hc : Sub M (s + 3 * i + 65 + flen k pe + flen k pf)
        (frag k pt (s + 3 * i + 65 + flen k pe + flen k pf) e) :=
      hs.at (by
        rw [List.length_append, List.length_append, List.length_append, length_preRows,
          length_testRows, length_frag, length_frag]
        omega)
    obtain ⟨T1, hT1, h1⟩ := test_full S hi hp ht X
    obtain ⟨X', T2, hT2, h2⟩ := ih hk (ok_sel k pe pf pt hok.2.1 hok.2.2.1 hok.2.2.2 _) M _ e
      (sub_sel ha hb hc _) W X (by omega)
    refine ⟨X', _, ?_, h1.trans h2⟩
    have : 40 * (t + 1) * W = 40 * t * W + 40 * W := by rw [Nat.mul_add, Nat.add_mul, Nat.mul_one]
    omega
  | @seq p q S S1 S2 t1 t2 hp _ ih1 ih2 =>
    intro hk hok M s e hs W X hW
    have h1s : Sub M s (frag k p s (s + flen k p)) := hs.left
    have h2s : Sub M (s + flen k p) (frag k q (s + flen k p) e) := hs.at (by rw [length_frag])
    have hl := hp.lay_le
    obtain ⟨X1, T1, hT1, h1⟩ := ih1 hk hok.1 M s _ h1s W X (by omega)
    obtain ⟨X2, T2, hT2, h2⟩ := ih2 (by rw [hp.len, hk]) hok.2 M _ e h2s W X1 (by omega)
    refine ⟨X2, _, ?_, h1.trans h2⟩
    have : 40 * (t1 + t2) * W = 40 * t1 * W + 40 * t2 * W := by rw [Nat.mul_add, Nat.add_mul]
    omega
  | @whT i me mf mt p S S1 S2 t1 t2 hm hp _ ih1 ih2 =>
    intro hk hok M s e hs W X hW
    have hi : i < S.length := by rw [hk]; exact hok.1
    have hpre : Sub M s (preRows s i (s + 3 * i + 2)) := hs.left.left
    have ht := hs.left.at (b' := s + 3 * i + 2) (by rw [length_preRows]; omega)
    have hb : Sub M (s + 3 * i + 65) (frag k p (s + 3 * i + 65) s) :=
      hs.at (by rw [List.length_append, length_preRows, length_testRows]; omega)
    obtain ⟨T0, hT0, h0⟩ := test_full S hi hpre ht X
    rw [tsel_if, hm, if_pos rfl] at h0
    have hl := hp.lay_le
    obtain ⟨X1, T1, hT1, h1⟩ := ih1 hk hok.2 M _ s hb W X (by omega)
    obtain ⟨X2, T2, hT2, h2⟩ := ih2 (by rw [hp.len, hk]) hok M s e hs W X1 (by omega)
    refine ⟨X2, _, ?_, h0.trans (h1.trans h2)⟩
    have : 40 * (t1 + t2 + 1) * W = 40 * t1 * W + 40 * t2 * W + 40 * W := by
      rw [Nat.mul_add, Nat.mul_add, Nat.add_mul, Nat.add_mul, Nat.mul_one]
    omega
  | @whF i me mf mt p S hm =>
    intro hk hok M s e hs W X hW
    have hi : i < S.length := by rw [hk]; exact hok.1
    have hpre : Sub M s (preRows s i (s + 3 * i + 2)) := hs.left.left
    have ht := hs.left.at (b' := s + 3 * i + 2) (by rw [length_preRows]; omega)
    obtain ⟨T0, hT0, h0⟩ := test_full S hi hpre ht X
    rw [tsel_if, hm] at h0
    exact ⟨X, T0, by omega, h0⟩
  | @skip S =>
    intro hk _ M s e hs W X hW
    obtain ⟨v1, v2, R, hR⟩ := lay_two S (by intro h; rw [h] at hk; simp at hk; omega) X
    have := tramp_ok hs v1 v2 R
    rw [← hR] at this
    exact ⟨X, 2, by omega, this⟩

end ZP.Cx
