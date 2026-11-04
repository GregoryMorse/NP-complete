module

public import ZP.Dx

@[expose] public section

/-!
# Target bounds

`TgLe B rows`: every `go` action in `rows` moves to a state `≤ B`. The machines
`DX V k m x` satisfy this with `B` their number of states (`tg_DX`), so their compiled
entries never need the clamp `min q (nS D)`.
-/

namespace ZP.Cx

def tgA (B : Nat) : Act → Prop
  | .halt _ => True
  | .go _ _ q => q ≤ B

def TgLe (B : Nat) : List (Act × Act × Act) → Prop
  | [] => True
  | r :: rs => (tgA B r.1 ∧ tgA B r.2.1 ∧ tgA B r.2.2) ∧ TgLe B rs

theorem tg_app (B : Nat) : ∀ (A C : List (Act × Act × Act)), TgLe B A → TgLe B C →
    TgLe B (A ++ C)
  | [], _, _, h => h
  | _ :: A, C, h1, h2 => ⟨h1.1, tg_app B A C h1.2 h2⟩

theorem tg_get (B : Nat) : ∀ (rows : List (Act × Act × Act)) (j : Nat) (r : Act × Act × Act),
    TgLe B rows → rows[j]? = some r → tgA B r.1 ∧ tgA B r.2.1 ∧ tgA B r.2.2
  | [], _, _, _, h => by simp at h
  | _ :: _, 0, r, h, e => by simp at e; subst e; exact h.1
  | _ :: rs, j + 1, r, h, e => tg_get B rs j r h.2 (by simpa using e)

theorem tgA_go {B : Nat} {w r : Bool} {q : Nat} (h : q ≤ B) : tgA B (.go w r q) := h

theorem tgA_H (B : Nat) : tgA B H := trivial

/-! ## Gadgets -/

section
variable {B : Nat}

theorem tg_ret {s e : Nat} (h1 : s + 20 ≤ B) (h2 : e ≤ B) : TgLe B (retRows s e) := by
  simp only [retRows, TgLe, tgA, same, H]
  and_intros <;> first | trivial | omega

theorem tg_tramp {s n : Nat} (h1 : s + 2 ≤ B) (h2 : n ≤ B) : TgLe B (tramp s n) := by
  simp only [tramp, TgLe, tgA, same, H]
  and_intros <;> first | trivial | omega

theorem tg_skip {s n : Nat} (h1 : s + 3 ≤ B) (h2 : n ≤ B) : TgLe B (skipRows s n) := by
  simp only [skipRows, TgLe, tgA, same, H]
  and_intros <;> first | trivial | omega

theorem tg_goto {e : Nat} (h2 : e ≤ B) : ∀ (i s : Nat), s + 3 * i ≤ B → TgLe B (gotoRows s e i)
  | 0, _, _ => trivial
  | i + 1, s, h => by
    refine tg_app B _ _ (tg_skip (by omega) ?_) (tg_goto h2 i (s + 3) (by omega))
    by_cases hi : i = 0
    · rw [if_pos hi]; exact h2
    · rw [if_neg hi]; omega

theorem tg_pre {s i ent : Nat} (h1 : s + 3 * i + 2 ≤ B) (h2 : ent ≤ B) :
    TgLe B (preRows s i ent) := by
  refine tg_app B _ _ (tg_tramp (by omega) ?_) (tg_goto h2 i (s + 2) (by omega))
  by_cases hi : i = 0
  · rw [if_pos hi]; exact h2
  · rw [if_neg hi]; omega

theorem tg_test {s ee ef et : Nat} (h1 : s + 63 ≤ B) (h2 : ee ≤ B) (h3 : ef ≤ B) (h4 : et ≤ B) :
    TgLe B (testRows s ee ef et) := by
  refine tg_app B _ _ (tg_app B _ _ (tg_app B _ _ ?_ (tg_ret (by omega) h3))
    (tg_ret (by omega) h4)) (tg_ret (by omega) h2)
  simp only [TgLe, tgA, same, H]
  and_intros <;> first | trivial | omega

theorem tg_block {s n : Nat} (h1 : s + 8 ≤ B) (h2 : n + 1 ≤ B) : TgLe B (blockRows s n) := by
  simp only [blockRows, TgLe, tgA, H]
  and_intros <;> first | trivial | omega

theorem tg_fin {f e : Nat} (h1 : f + 24 ≤ B) (h2 : e ≤ B) : TgLe B (finRows f e) := by
  refine tg_app B _ _ ?_ (tg_ret (by omega) h2)
  simp only [TgLe, tgA, anyA]
  and_intros <;> first | trivial | omega

theorem tg_push {e : Nat} (h2 : e ≤ B) : ∀ (c s : Nat), s + 8 * c + 24 ≤ B →
    TgLe B (pushRows s e c)
  | 0, _, h => tg_fin (by omega) h2
  | c + 1, s, h => tg_app B _ _ (tg_block (by omega) (by omega)) (tg_push h2 c (s + 8) (by omega))

theorem tg_popBlk {b n : Nat} (h1 : b + 21 ≤ B) (h2 : n ≤ B) : TgLe B (popBlk b n) := by
  simp only [popBlk, TgLe, tgA, same, anyA, H]
  and_intros <;> first | trivial | omega

theorem tg_popBlocks {e : Nat} (h2 : e ≤ B) : ∀ (c b : Nat), b + 21 * c + 20 ≤ B →
    TgLe B (popBlocks b e c)
  | 0, _, h => tg_ret (by omega) h2
  | c + 1, b, h => tg_app B _ _ (tg_popBlk (by omega) (by omega))
      (tg_popBlocks h2 c (b + 21) (by omega))

theorem tg_popRows {s e c : Nat} (h1 : s + 21 * c + 63 ≤ B) (h2 : e ≤ B) :
    TgLe B (popRows s e c) := by
  refine tg_app B _ _ (tg_app B _ _ ?_ (tg_ret (by omega) h2))
    (tg_popBlocks h2 (c + 1) (s + 22) (by omega))
  simp only [TgLe, tgA, same, H]
  and_intros <;> first | trivial | omega

theorem p0_le (s : Nat) (u1 u2 : Bool) : p0 s u1 u2 ≤ s + 3 := by
  unfold p0 bn; cases u1 <;> cases u2 <;> simp

theorem tg_frag (k : Nat) : ∀ (c : Cmd) (s e : Nat), e ≤ B → s + flen k c ≤ B →
    TgLe B (frag k c s e)
  | .push i b, s, e, he, h => by
    have h' : s + (3 * i + 2 + (8 * (k - i) + 24)) ≤ B := h
    have hp := p0_le (s + 3 * i + 2) true b
    exact tg_app B _ _ (tg_pre (by omega) (by omega)) (tg_push he _ _ (by omega))
  | .pop i, s, e, he, h => by
    have h' : s + (3 * i + 2 + (21 * (k - i - 1) + 63)) ≤ B := h
    exact tg_app B _ _ (tg_pre (by omega) (by omega)) (tg_popRows (by omega) he)
  | .cs i a b c, s, e, he, h => by
    have h' : s + (3 * i + 2 + 63 + flen k a + flen k b + flen k c) ≤ B := h
    exact tg_app B _ _ (tg_app B _ _ (tg_app B _ _ (tg_app B _ _
      (tg_pre (by omega) (by omega)) (tg_test (by omega) (by omega) (by omega) (by omega)))
      (tg_frag k a _ e he (by omega))) (tg_frag k b _ e he (by omega)))
      (tg_frag k c _ e he (by omega))
  | .seq p q, s, e, he, h => by
    have h' : s + (flen k p + flen k q) ≤ B := h
    exact tg_app B _ _ (tg_frag k p s _ (by omega) (by omega)) (tg_frag k q _ e he (by omega))
  | .wh i me mf mt p, s, e, he, h => by
    have h' : s + (3 * i + 2 + 63 + flen k p) ≤ B := h
    refine tg_app B _ _ (tg_app B _ _ (tg_pre (by omega) (by omega)) (tg_test (by omega) ?_ ?_ ?_))
      (tg_frag k p _ s (by omega) (by omega))
    all_goals split <;> omega
  | .skip, s, e, he, h => by
    have h' : s + 2 ≤ B := h
    exact tg_tramp (by omega) he

theorem tg_sep {e : Nat} (h2 : e ≤ B) : ∀ (m s : Nat), s + 2 * m + 2 ≤ B → TgLe B (sepRows s e m)
  | 0, s, h => by
    simp only [sepRows, TgLe, tgA, anyA]
    and_intros <;> first | trivial | omega
  | m + 1, s, h => by
    refine tg_app B _ _ ?_ (tg_sep h2 m (s + 2) (by omega))
    simp only [TgLe, tgA, anyA]
    and_intros <;> first | trivial | omega

theorem tg_vskip {s n : Nat} (last : Bool) (h1 : s + 2 ≤ B) (h2 : n ≤ B) :
    TgLe B (vskipRows s n last) := by
  simp only [vskipRows, TgLe, tgA, same, H]
  and_intros <;> first | trivial | omega

theorem tg_xrows {e : Nat} (h2 : e ≤ B) : ∀ (x : List Bool) (f : Nat), f + 2 * x.length + 2 ≤ B →
    TgLe B (xrows f e x)
  | [], f, h => by
    simp only [List.length_nil] at h
    simp only [xrows, TgLe, tgA, H]
    and_intros <;> first | trivial | omega
  | b :: x, f, h => by
    simp only [List.length_cons] at h
    refine tg_app B _ _ ?_ (tg_xrows h2 x (f + 2) (by omega))
    cases b <;> (simp only [bitRow, TgLe, tgA, H]; and_intros <;> first | trivial | omega)

end

theorem length_DX (V : Mach) (k m : Nat) (x : List Bool) :
    (DX V k m x).tbl.length = F0 V k m + 2 * x.length + 2 := by
  show (fxRows V k m ++ xrows (F0 V k m) 1 x).length = _
  rw [List.length_append, length_fxRows, length_xrows]
  omega

theorem tg_DX (V : Mach) (k m : Nat) (x : List Bool) :
    TgLe (DX V k m x).tbl.length (DX V k m x).tbl := by
  rw [length_DX]
  have hF : F0 V k m = 68 + flen 12 (BODY V k m) := rfl
  refine tg_app _ _ _ ?_ (tg_xrows (by omega) x _ (by omega))
  unfold fxRows
  refine tg_app _ _ _ (tg_app _ _ _ (tg_app _ _ _ (tg_app _ _ _ (tg_app _ _ _ (tg_app _ _ _
    (tg_app _ _ _ ?_ (tg_ret (by omega) (by omega))) (tg_vskip false (by omega) (by omega)))
    (tg_vskip false (by omega) (by omega))) (tg_sep (by omega) 9 27 (by omega)))
    (tg_ret (by omega) (by omega))) (tg_frag 12 (BODY V k m) 67 _ (by omega) (by omega))) ?_
  · simp only [TgLe, tgA, same, H]
    and_intros <;> first | trivial | omega
  · simp only [TgLe, tgA, H]
    and_intros <;> trivial

end ZP.Cx
