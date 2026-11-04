module

public import ZP.Prog

@[expose] public section

/-!
# A library of stack programs

`ExecB c S S' B`: `c` runs from `S` to `S'` within `B` operations. Macros, each
with its specification on an arbitrary list of stacks:

* `mv1 i j`: move the top of stack `i` (if any) onto stack `j`.
* `mv i j`: move all of stack `i` onto `j` (reversing it).
* `clr i`: empty stack `i`.
* `r1 i t`: rotate stack `i` by one (top to bottom), using an empty stack `t`.
* `rotk r t k`: the guest rotation `rot` on stack `r`, pushing `entryOnes` ones on `k`.
* `rotq r t j`: the guest rotation `rot`, with an empty scratch stack `j`.
-/

namespace ZP.Cx

/-! ## Lists of stacks -/

theorem getD_set : ∀ (S : List (List Bool)) (i j : Nat) (v : List Bool),
    (S.set i v).getD j [] = if j = i ∧ i < S.length then v else S.getD j []
  | [], i, j, v => by simp
  | x :: S, 0, 0, v => by simp
  | x :: S, 0, j + 1, v => by simp
  | x :: S, i + 1, 0, v => by simp
  | x :: S, i + 1, j + 1, v => by
    have e1 : ((x :: S).set (i + 1) v).getD (j + 1) [] = (S.set i v).getD j [] := by
      first | rfl | simp
    have e2 : (x :: S).getD (j + 1) [] = S.getD j [] := by first | rfl | simp
    rw [e1, e2, getD_set S i j v]
    simp

theorem getD_set_eq {S : List (List Bool)} {i : Nat} (v : List Bool) (h : i < S.length) :
    (S.set i v).getD i [] = v := by
  rw [getD_set]; simp [h]

theorem getD_set_ne {S : List (List Bool)} {i j : Nat} (v : List Bool) (h : j ≠ i) :
    (S.set i v).getD j [] = S.getD j [] := by
  rw [getD_set]; simp [h]

theorem stk_ext : ∀ (S S' : List (List Bool)), S.length = S'.length →
    (∀ j, S.getD j [] = S'.getD j []) → S = S'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: S, y :: S', h, hj => by
    have e : x = y := by simpa using hj 0
    rw [e, stk_ext S S' (by simpa using h) (fun j => by simpa using hj (j + 1))]

/-- Prove an equation between lists of stacks, index by index. -/
macro "stk_eq" : tactic => `(tactic| (
  refine stk_ext _ _ (by simp only [List.length_set]) (fun j => ?_)
  simp only [getD_set, List.length_set]
  repeat' split
  all_goals first | (simp_all; done) | omega | simp_all))

/-! ## Bounded runs -/

def ExecB (c : Cmd) (S S' : List (List Bool)) (B : Nat) : Prop := ∃ t, t ≤ B ∧ Exec c S S' t

theorem ExecB.to {c : Cmd} {S S1 S2 : List (List Bool)} {B B2 : Nat} (h : ExecB c S S1 B)
    (e : S1 = S2) (hb : B ≤ B2) : ExecB c S S2 B2 := by
  obtain ⟨t, ht, h⟩ := h
  subst e
  exact ⟨t, by omega, h⟩

theorem ExecB.seq {p q : Cmd} {S S1 S2 : List (List Bool)} {B1 B2 : Nat} (h1 : ExecB p S S1 B1)
    (h2 : ExecB q S1 S2 B2) : ExecB (.seq p q) S S2 (B1 + B2) := by
  obtain ⟨t1, ht1, h1⟩ := h1
  obtain ⟨t2, ht2, h2⟩ := h2
  exact ⟨t1 + t2, by omega, .seq h1 h2⟩

theorem ExecB.cs {i : Nat} {pe pf pt : Cmd} {S S' : List (List Bool)} {B : Nat}
    (h : ExecB (sel (S.getD i []) pe pf pt) S S' B) : ExecB (.cs i pe pf pt) S S' (B + 1) := by
  obtain ⟨t, ht, h⟩ := h
  exact ⟨t + 1, by omega, .cs h⟩

theorem ExecB.whT {i : Nat} {me mf mt : Bool} {p : Cmd} {S S1 S2 : List (List Bool)} {B1 B2 : Nat}
    (hm : sel (S.getD i []) me mf mt = true) (h1 : ExecB p S S1 B1)
    (h2 : ExecB (.wh i me mf mt p) S1 S2 B2) : ExecB (.wh i me mf mt p) S S2 (B1 + B2 + 1) := by
  obtain ⟨t1, ht1, h1⟩ := h1
  obtain ⟨t2, ht2, h2⟩ := h2
  exact ⟨t1 + t2 + 1, by omega, .whT hm h1 h2⟩

theorem ExecB.whF {i : Nat} {me mf mt : Bool} {p : Cmd} {S : List (List Bool)}
    (hm : sel (S.getD i []) me mf mt = false) : ExecB (.wh i me mf mt p) S S 1 :=
  ⟨1, Nat.le_refl _, .whF hm⟩

theorem ExecB.push {i : Nat} {b : Bool} {S : List (List Bool)} :
    ExecB (.push i b) S (S.set i (b :: S.getD i [])) 1 := ⟨1, Nat.le_refl _, .push⟩

theorem ExecB.pop {i : Nat} {S : List (List Bool)} :
    ExecB (.pop i) S (S.set i (S.getD i []).tail) 1 := ⟨1, Nat.le_refl _, .pop⟩

theorem ExecB.skip {S : List (List Bool)} : ExecB .skip S S 1 := ⟨1, Nat.le_refl _, .skip⟩

theorem sel_head {me mf mt : Bool} : ∀ (l : List Bool) (b : Bool), l.head? = some b →
    sel l me mf mt = if b then mt else mf
  | [], _, h => by simp at h
  | false :: _, b, h => by simp at h; subst h; rfl
  | true :: _, b, h => by simp at h; subst h; rfl

/-! ## Moving and clearing -/

def mvb (i j : Nat) (b : Bool) : Cmd := .seq (.pop i) (.push j b)

def mv1 (i j : Nat) : Cmd := .cs i .skip (mvb i j false) (mvb i j true)

def mv (i j : Nat) : Cmd := .wh i false true true (mv1 i j)

def clr (i : Nat) : Cmd := .wh i false true true (.pop i)

theorem mv1_cons {S : List (List Bool)} {i j : Nat} {b : Bool} {u : List Bool} (hij : i ≠ j)
    (h : S.getD i [] = b :: u) :
    ExecB (mv1 i j) S ((S.set i u).set j (b :: S.getD j [])) 3 := by
  have hp : ExecB (mvb i j b) S ((S.set i u).set j (b :: S.getD j [])) 2 := by
    refine (ExecB.pop.seq ExecB.push).to ?_ (Nat.le_refl _)
    rw [h, List.tail_cons, getD_set_ne _ (Ne.symm hij)]
  refine ExecB.cs (by rw [h]; cases b <;> exact hp)

theorem mv1_nil {S : List (List Bool)} {i j : Nat} (h : S.getD i [] = []) :
    ExecB (mv1 i j) S S 2 :=
  ExecB.cs (by rw [h]; exact ExecB.skip)

theorem mv_ok {i j : Nat} (hij : i ≠ j) : ∀ (u : List Bool) (S : List (List Bool)),
    i < S.length → j < S.length → S.getD i [] = u →
      ExecB (mv i j) S ((S.set i []).set j (u.reverse ++ S.getD j [])) (4 * u.length + 1)
  | [], S, hi, hj, h => by
    refine (ExecB.whF (by rw [h]; rfl)).to ?_ (by omega)
    stk_eq
  | b :: u, S, hi, hj, h => by
    have h1 := mv1_cons hij h
    have h2 := mv_ok hij u ((S.set i u).set j (b :: S.getD j [])) (by simpa using hi)
      (by simpa using hj) (by rw [getD_set_ne _ hij, getD_set_eq _ hi])
    refine (ExecB.whT (by rw [h]; cases b <;> rfl) h1 h2).to ?_
      (by simp only [List.length_cons]; omega)
    stk_eq

theorem clr_ok {i : Nat} : ∀ (u : List Bool) (S : List (List Bool)), i < S.length →
    S.getD i [] = u → ExecB (clr i) S (S.set i []) (2 * u.length + 1)
  | [], S, hi, h => by
    refine (ExecB.whF (by rw [h]; rfl)).to ?_ (by omega)
    stk_eq
  | b :: u, S, hi, h => by
    have h1 : ExecB (.pop i) S (S.set i u) 1 := ExecB.pop.to (by rw [h, List.tail_cons]) (Nat.le_refl _)
    have h2 := clr_ok u (S.set i u) (by simpa using hi) (getD_set_eq _ hi)
    refine (ExecB.whT (by rw [h]; cases b <;> rfl) h1 h2).to ?_
      (by simp only [List.length_cons]; omega)
    stk_eq

/-! ## Rotation by one -/

@[simp] def r1f : List Bool → List Bool
  | [] => []
  | b :: l => l ++ [b]

def r1b (i t : Nat) (b : Bool) : Cmd := .seq (.pop i) (.seq (mv i t) (.seq (.push i b) (mv t i)))

def r1 (i t : Nat) : Cmd := .cs i .skip (r1b i t false) (r1b i t true)

theorem r1_ok {S : List (List Bool)} {i t : Nat} (hit : i ≠ t) (hi : i < S.length)
    (ht : t < S.length) (hT : S.getD t [] = []) :
    ExecB (r1 i t) S (S.set i (r1f (S.getD i []))) (8 * (S.getD i []).length + 6) := by
  cases h : S.getD i [] with
  | nil =>
    refine (ExecB.cs (by rw [h]; exact ExecB.skip)).to ?_ (by omega)
    stk_eq
  | cons b l =>
    have e1 : ExecB (.pop i) S (S.set i l) 1 := ExecB.pop.to (by rw [h, List.tail_cons]) (Nat.le_refl _)
    have e2 := mv_ok hit l (S.set i l) (by simpa using hi) (by simpa using ht) (getD_set_eq _ hi)
    have e3 := ExecB.push (i := i) (b := b) (S := ((S.set i l).set i []).set t
      (l.reverse ++ (S.set i l).getD t []))
    have e4 := mv_ok (Ne.symm hit) l.reverse
      ((((S.set i l).set i []).set t (l.reverse ++ (S.set i l).getD t [])).set i
        (b :: (((S.set i l).set i []).set t (l.reverse ++ (S.set i l).getD t [])).getD i []))
      (by simpa using ht) (by simpa using hi)
      (by rw [getD_set_ne _ (Ne.symm hit), getD_set_eq _ (by simpa using ht),
        getD_set_ne _ (Ne.symm hit), hT, List.append_nil])
    have hb : ExecB (r1b i t b) S (S.set i (l ++ [b])) (8 * l.length + 4) := by
      refine (e1.seq (e2.seq (e3.seq e4))).to ?_ (by simp only [List.length_reverse]; omega)
      stk_eq
    have hb' : ExecB (sel (b :: l) .skip (r1b i t false) (r1b i t true)) S (S.set i (l ++ [b]))
        (8 * l.length + 4) := by
      cases b <;> exact hb
    refine (ExecB.cs (by rw [h]; exact hb')).to rfl (by simp only [List.length_cons]; omega)

/-! ## Rotations of the guest code -/

def rr : Nat → List Bool → List Bool
  | 0, R => R
  | m + 1, R => r1f (rr m R)

theorem length_r1f : ∀ R : List Bool, (r1f R).length = R.length
  | [] => rfl
  | b :: l => by simp [r1f]

theorem length_rr (R : List Bool) : ∀ m, (rr m R).length = R.length
  | 0 => rfl
  | m + 1 => by
    show (r1f (rr m R)).length = _
    rw [length_r1f, length_rr R m]

theorem mem_r1f {a : Bool} : ∀ {R : List Bool}, a ∈ R → a ∈ r1f R
  | [], h => h
  | _ :: l, h => by
    cases h with
    | head => simp [r1f]
    | tail _ h => simp [r1f, h]

theorem mem_rr {a : Bool} {R : List Bool} (h : a ∈ R) : ∀ m, a ∈ rr m R
  | 0 => h
  | m + 1 => mem_r1f (mem_rr h m)

theorem mod_succ (m n : Nat) (hn : 0 < n) :
    (m + 1) % n = if m % n + 1 < n then m % n + 1 else 0 := by
  rw [Nat.add_mod]
  by_cases h1 : n = 1
  · subst h1; simp
  · rw [Nat.mod_eq_of_lt (show 1 < n by omega)]
    split
    · exact Nat.mod_eq_of_lt ‹_›
    · have : m % n + 1 = n := by have := Nat.mod_lt m hn; omega
      rw [this, Nat.mod_self]

theorem rr_eq (R : List Bool) (m : Nat) :
    rr m R = R.drop (m % R.length) ++ R.take (m % R.length) := by
  induction m with
  | zero => simp [rr]
  | succ m ih =>
    show r1f (rr m R) = _
    rw [ih]
    by_cases hR : R = []
    · subst hR; simp [r1f]
    · have hn : 0 < R.length := by
        cases R with
        | nil => exact absurd rfl hR
        | cons _ _ => simp
      rw [mod_succ m R.length hn]
      have ha := Nat.mod_lt m hn
      generalize m % R.length = a at ha ⊢
      rw [List.drop_eq_getElem_cons ha]
      show (R.drop (a + 1) ++ R.take a) ++ [R[a]] = _
      have e : R.take a ++ [R[a]] = R.take (a + 1) := by
        rw [List.take_succ, List.getElem?_eq_getElem ha]
        all_goals rfl
      split
      · rw [List.append_assoc, e]
      · have hd : R.drop (a + 1) = [] := List.drop_of_length_le (by omega)
        have ht : R.take (a + 1) = R := List.take_of_length_le (by omega)
        rw [List.append_assoc, e, hd, ht]
        simp

theorem head_rr (R : List Bool) (hR : R ≠ []) (m : Nat) : (rr m R).head? = some (cyc R m) := by
  have hn : 0 < R.length := by
    cases R with
    | nil => exact absurd rfl hR
    | cons _ _ => simp
  rw [rr_eq, List.drop_eq_getElem_cons (Nat.mod_lt m hn)]
  show some R[m % R.length] = some (R.getD (m % R.length) false)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (Nat.mod_lt m hn)]
  all_goals rfl

theorem exists_zero (R : List Bool) (hR : false ∈ R) (i : Nat) :
    ∃ d, d < R.length ∧ cyc R (i + d) = false := by
  obtain ⟨p, hp, hpv⟩ := List.mem_iff_getElem.mp hR
  have hn : 0 < R.length := by omega
  have hc : ∀ d, d < R.length → (i % R.length + d) % R.length = p → cyc R (i + d) = false := by
    intro d hd he
    unfold cyc
    rw [Nat.add_mod, Nat.mod_eq_of_lt hd, he, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hp, hpv]
    all_goals rfl
  have ha := Nat.mod_lt i hn
  generalize i % R.length = a at ha hc
  by_cases h : a ≤ p
  · exact ⟨p - a, by omega, hc _ (by omega)
      (by rw [show a + (p - a) = p by omega, Nat.mod_eq_of_lt hp])⟩
  · exact ⟨p + R.length - a, by omega, hc _ (by omega)
      (by rw [show a + (p + R.length - a) = p + R.length by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hp])⟩

theorem onesFrom_le (R : List Bool) : ∀ f i, onesFrom R f i ≤ f
  | 0, _ => Nat.le_refl _
  | f + 1, i => by
    have := onesFrom_le R f (i + 1)
    simp only [onesFrom]
    split <;> omega

theorem rot_rr (R : List Bool) : rot R = rr (entryOnes R + 3) R := by
  rw [rr_eq]; rfl

theorem length_rot (R : List Bool) : (rot R).length = R.length := by
  rw [rot_rr, length_rr]

theorem mem_rot {a : Bool} {R : List Bool} (h : a ∈ R) : a ∈ rot R := by
  rw [rot_rr]; exact mem_rr h _

theorem length_rotN : ∀ (m : Nat) (R : List Bool), (rotN m R).length = R.length
  | 0, _ => rfl
  | m + 1, R => by
    show (rotN m (rot R)).length = _
    rw [length_rotN m (rot R), length_rot]

theorem mem_rotN {a : Bool} : ∀ (m : Nat) {R : List Bool}, a ∈ R → a ∈ rotN m R
  | 0, _, h => h
  | m + 1, _, h => mem_rotN m (mem_rot h)

/-! ## The guest rotation as a stack program -/

def rloop (r t k : Nat) : Cmd := .wh r false false true (.seq (r1 r t) (.push k true))

def rotk (r t k : Nat) : Cmd := .seq (r1 r t) (.seq (r1 r t) (.seq (rloop r t k) (r1 r t)))

def rotq (r t j : Nat) : Cmd := .seq (rotk r t j) (clr j)

theorem rloop_ok {r t k : Nat} (h1 : r ≠ t) (h2 : r ≠ k) (h3 : t ≠ k) (R : List Bool)
    (hR : R ≠ []) : ∀ (f i : Nat) (S : List (List Bool)), r < S.length → t < S.length →
      k < S.length → (∃ d, d < f ∧ cyc R (i + d) = false) → S.getD r [] = rr i R →
      S.getD t [] = [] →
      ExecB (rloop r t k) S
        ((S.set r (rr (i + onesFrom R f i) R)).set k
          (List.replicate (onesFrom R f i) true ++ S.getD k []))
        (onesFrom R f i * (8 * R.length + 8) + 1)
  | 0, i, S, _, _, _, ⟨d, hd, _⟩, _, _ => absurd hd (Nat.not_lt_zero _)
  | f + 1, i, S, hr, ht, hk, hz, hS, hT => by
    have hh := head_rr R hR i
    cases hc : cyc R i with
    | false =>
      have ho : onesFrom R (f + 1) i = 0 := by simp [onesFrom, hc]
      rw [ho]
      refine (ExecB.whF ?_).to ?_ (by omega)
      · rw [hS, sel_head _ false (by rw [hh, hc])]; all_goals rfl
      · stk_eq
    | true =>
      have ho : onesFrom R (f + 1) i = onesFrom R f (i + 1) + 1 := by simp [onesFrom, hc]
      rw [ho]
      have hb1 := r1_ok h1 hr ht hT
      rw [hS] at hb1
      have hb : ExecB (.seq (r1 r t) (.push k true)) S
          ((S.set r (rr (i + 1) R)).set k (true :: S.getD k [])) (8 * R.length + 7) := by
        refine (hb1.seq ExecB.push).to ?_ ?_
        · rw [getD_set_ne _ (Ne.symm h2)]; rfl
        · have := length_rr R i; omega
      obtain ⟨d, hd, hdz⟩ := hz
      have hd0 : d ≠ 0 := by
        intro e; subst e; simp [hc] at hdz
      have hz' : ∃ d, d < f ∧ cyc R (i + 1 + d) = false :=
        ⟨d - 1, by omega, by rw [show i + 1 + (d - 1) = i + d by omega]; exact hdz⟩
      have ih := rloop_ok h1 h2 h3 R hR f (i + 1)
        ((S.set r (rr (i + 1) R)).set k (true :: S.getD k []))
        (by simpa using hr) (by simpa using ht) (by simpa using hk) hz'
        (by rw [getD_set_ne _ h2, getD_set_eq _ hr])
        (by rw [getD_set_ne _ h3, getD_set_ne _ (Ne.symm h1), hT])
      refine (ExecB.whT ?_ hb ih).to ?_ ?_
      · rw [hS, sel_head _ true (by rw [hh, hc])]; all_goals rfl
      · rw [show i + 1 + onesFrom R f (i + 1) = i + (onesFrom R f (i + 1) + 1) by omega,
          List.replicate_succ', List.append_assoc]
        stk_eq
      · rw [Nat.add_mul, Nat.one_mul]; omega

theorem rotk_ok {r t k : Nat} (h1 : r ≠ t) (h2 : r ≠ k) (h3 : t ≠ k) {S : List (List Bool)}
    (hr : r < S.length) (ht : t < S.length) (hk : k < S.length) {R : List Bool}
    (h0 : false ∈ R) (hS : S.getD r [] = R) (hT : S.getD t [] = []) :
    ExecB (rotk r t k) S ((S.set r (rot R)).set k (List.replicate (entryOnes R) true ++ S.getD k []))
      ((R.length + 3) * (8 * R.length + 8) + 1) := by
  have hR : R ≠ [] := by intro e; subst e; simp at h0
  have a1 := r1_ok h1 hr ht hT
  rw [hS] at a1
  have a2 := r1_ok h1 (by simpa using hr) (by simpa using ht)
    (by rw [getD_set_ne _ (Ne.symm h1), hT] : (S.set r (r1f R)).getD t [] = [])
  rw [getD_set_eq _ hr] at a2
  have a3 := rloop_ok h1 h2 h3 R hR R.length 2 ((S.set r (r1f R)).set r (r1f (r1f R)))
    (by simpa using hr) (by simpa using ht) (by simpa using hk)
    (by obtain ⟨d, hd, hz⟩ := exists_zero R h0 2; exact ⟨d, hd, hz⟩)
    (by rw [getD_set_eq _ (by simpa using hr)]; all_goals rfl)
    (by rw [getD_set_ne _ (Ne.symm h1), getD_set_ne _ (Ne.symm h1), hT])
  have hS3 : ∀ (X : List Bool), ((((S.set r (r1f R)).set r (r1f (r1f R))).set r
      (rr (2 + onesFrom R R.length 2) R)).set k X).getD t [] = [] := by
    intro X
    rw [getD_set_ne _ h3, getD_set_ne _ (Ne.symm h1), getD_set_ne _ (Ne.symm h1),
      getD_set_ne _ (Ne.symm h1), hT]
  have a4 := r1_ok h1 (by simpa using hr) (by simpa using ht)
    (hS3 (List.replicate (onesFrom R R.length 2) true ++
      ((S.set r (r1f R)).set r (r1f (r1f R))).getD k []))
  rw [getD_set_ne _ h2, getD_set_eq _ (by simpa using hr)] at a4
  have he : entryOnes R = onesFrom R R.length 2 := rfl
  have hl : onesFrom R R.length 2 ≤ R.length := onesFrom_le R _ _
  refine (a1.seq (a2.seq (a3.seq a4))).to ?_ ?_
  · rw [rot_rr, he, show onesFrom R R.length 2 + 3 = (2 + onesFrom R R.length 2) + 1 by omega]
    show _ = (S.set r (r1f (rr (2 + onesFrom R R.length 2) R))).set k _
    stk_eq
  · rw [length_r1f, length_rr]
    have hm : onesFrom R R.length 2 * (8 * R.length + 8) ≤ R.length * (8 * R.length + 8) :=
      Nat.mul_le_mul_right _ hl
    rw [Nat.add_mul]
    omega

/-- Bound for one guest rotation `rotq` on a code of length `n`. -/
def rB (n : Nat) : Nat := (n + 3) * (8 * n + 8) + 2 * n + 3

theorem rotq_ok {r t j : Nat} (h1 : r ≠ t) (h2 : r ≠ j) (h3 : t ≠ j) {S : List (List Bool)}
    (hr : r < S.length) (ht : t < S.length) (hj : j < S.length) {R : List Bool}
    (h0 : false ∈ R) (hS : S.getD r [] = R) (hT : S.getD t [] = []) (hJ : S.getD j [] = []) :
    ExecB (rotq r t j) S (S.set r (rot R)) (rB R.length) := by
  have a1 := rotk_ok h1 h2 h3 hr ht hj h0 hS hT
  rw [hJ, List.append_nil] at a1
  have a2 := clr_ok (List.replicate (entryOnes R) true)
    ((S.set r (rot R)).set j (List.replicate (entryOnes R) true)) (by simpa using hj)
    (getD_set_eq _ (by simpa using hj))
  have hl : entryOnes R ≤ R.length := onesFrom_le R _ _
  refine (a1.seq a2).to ?_ ?_
  · stk_eq
  · simp only [List.length_replicate, rB]; omega

end ZP.Cx
