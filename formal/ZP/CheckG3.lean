module

public import ZP.CheckG2

@[expose] public section

/-! # The check phase of the GI machine (part 3): the `H` region with `c` passed entries -/

namespace ZP.G

open ZP

/-- The tape of `H` (entry tails `hs`, first cells `3`) in which the first `c` entries are passed
(first cell marked).  Entries are separated by `M`; the last one is followed by the blank. -/
def HP : List (List Nat) → Nat → List Nat
  | [], _ => []
  | [t], c => (if 0 < c then 2 else 3) :: t
  | t :: u :: ts, c => (if 0 < c then 2 else 3) :: (t ++ 1 :: HP (u :: ts) (c - 1))

theorem HP_sym4 : ∀ (hs : List (List Nat)) (c : Nat), (∀ t ∈ hs, Bits t) → Sym4 (HP hs c)
  | [], _, _ => Sym4.nil
  | [t], c, h => by
    have ht := h t (List.mem_cons_self ..)
    refine Sym4.cons ?_ ht.sym4
    split <;> simp [ALL]
  | t :: u :: ts, c, h => by
    have ht := h t (List.mem_cons_self ..)
    have := HP_sym4 (u :: ts) (c - 1) (fun s hs => h s (List.mem_cons_of_mem _ hs))
    refine Sym4.cons ?_ (ht.sym4.app (Sym4.cons (by simp [ALL]) this))
    split <;> simp [ALL]

theorem HP_split : ∀ (hs : List (List Nat)) (c : Nat), c < hs.length →
    ∃ Rest0 : List Nat, HP hs c = MP (hs.take c) ++ 3 :: Rest0 ∧ HP hs (c + 1) = MP (hs.take c) ++ 2 :: Rest0
  | [], c, h => by simp at h
  | [t], c, h => by
    have : c = 0 := by simp at h; omega
    subst this
    exact ⟨t, by simp [HP, MP], by simp [HP, MP]⟩
  | t :: u :: ts, 0, h => ⟨t ++ 1 :: HP (u :: ts) 0, by simp [HP, MP], by simp [HP, MP]⟩
  | t :: u :: ts, c + 1, h => by
    obtain ⟨R0, h1, h2⟩ := HP_split (u :: ts) c (by simp at h ⊢; omega)
    refine ⟨R0, ?_, ?_⟩
    · simp [HP, MP, h1]
    · simp [HP, MP, h2]

theorem HP_full : ∀ (hs : List (List Nat)), hs ≠ [] →
    ∃ tl, HP hs hs.length = MP hs.dropLast ++ 2 :: tl ∧ hs.getLast? = some tl
  | [], h => absurd rfl h
  | [t], _ => ⟨t, by simp [HP, MP], by simp⟩
  | t :: u :: ts, _ => by
    obtain ⟨tl, h1, h2⟩ := HP_full (u :: ts) (by simp)
    refine ⟨tl, ?_, ?_⟩
    · simp [HP, MP, h1]
      exact h1
    · simpa using h2

end ZP.G
