module

public import ZP.PairN3

@[expose] public section

/-! # The pair lemma of the NTT machine, part 4: the initialisation loop -/

namespace ZP.N

open ZP ZP.G

/-- The tail of a record (after its `MM`): header `F O P`, acc, E, z, u. -/
def Tail3 (o s u : Nat) : List Nat := [2, o, 2] ++ Fld s ++ Fld s ++ Fld s ++ Fld u

/-- A record after the initialisation: `P := p`, `E := 1`. -/
def RecI (p o s u : Nat) : List Nat := [1, 1, 2, o, p] ++ Fld s ++ E1 s ++ Fld s ++ Fld u

def recsI (s : Nat) : List (Nat × Nat) → List Nat
  | [] => []
  | (o, u) :: l => RecI 2 o s u ++ recsI s l

theorem Rec3_eq (o s u : Nat) : Rec3 o s u = [1, 1] ++ Tail3 o s u := by
  simp [Rec3, Tail3, List.append_assoc]

theorem noB_Tail3 (o s u : Nat) (ho : o = 2 ∨ o = 3) : NoB (Tail3 o s u) := fun x hx =>
  noB_Rec3 o s u ho x (by rw [Rec3_eq]; simp [hx])

theorem Fld_u4 (s : Nat) : ∀ a ∈ Fld s, a ∈ U4 := by
  intro a ha
  simp only [Fld, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_replicate] at ha
  rcases ha with (h | h) | ⟨_, h⟩ <;> simp [U4, h]

theorem E1_u4 (s : Nat) : ∀ a ∈ E1 s, a ∈ U4 := by
  intro a ha
  simp only [E1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_replicate] at ha
  rcases ha with (h | h | h) | ⟨_, h⟩ <;> simp [U4, h]

theorem RecI_u4 (p o s u : Nat) (hp : p = 2 ∨ p = 3) (ho : o = 2 ∨ o = 3) : ∀ a ∈ RecI p o s u, a ∈ U4 := by
  intro a ha
  simp only [RecI, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with (((h | h) | h) | h) | h
  · rcases h with h | h | h | h | h <;> simp [U4, h] <;> omega
  · exact Fld_u4 _ a h
  · exact E1_u4 _ a h
  · exact Fld_u4 _ a h
  · exact Fld_u4 _ a h

theorem u4_two (A : List Nat) (hA : ∀ a ∈ A, a ∈ U4) : ∀ a ∈ A ++ [1, 1], a ∈ U4 := by
  intro a ha
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h | h | h
  · exact hA a h
  all_goals simp [U4, h]

theorem initLoop0 (s : Nat) : ∀ (l : List (Nat × Nat)), (∀ x ∈ l, x.1 = 2 ∨ x.1 = 3) →
    ∀ (A : List Nat), (∀ a ∈ A, a ∈ U4) → ∀ o u, (o = 2 ∨ o = 3) →
    znttLogic.Reach
      (hdR QN.WH0 (A ++ [1, 1]) (Tail3 o s u ++ recsL s l))
      (hd QN.RZ0 (A ++ RecI 2 o s u ++ recsI s l) [0])
  | [], _, A, hA, o, u, ho => by
    have := recInitLast0 (A ++ [1, 1]) (u4_two A hA) o s u ho
    refine this.of_eq ?_ ?_
    · simp [Tail3, recsL, List.append_assoc]
    · simp [RecI, recsI, List.append_assoc]
  | (o', u') :: l, hl, A, hA, o, u, ho => by
    have ho' : o' = 2 ∨ o' = 3 := hl (o', u') (by simp)
    have hl' : ∀ x ∈ l, x.1 = 2 ∨ x.1 = 3 := fun x hx => hl x (by simp [hx])
    have h1 := recInitMid0 (A ++ [1, 1]) (u4_two A hA) o s u ho (Tail3 o' s u' ++ recsL s l)
      (noB_app (noB_Tail3 o' s u' ho') (noB_recsL s l hl'))
    have h2 := initLoop0 s l hl' (A ++ RecI 2 o s u) (by
      intro a ha
      simp only [List.mem_append] at ha
      rcases ha with h | h
      · exact hA a h
      · exact RecI_u4 2 o s u (Or.inl rfl) ho a h) o' u' ho'
    have h1' : znttLogic.Reach
        (hdR QN.WH0 (A ++ [1, 1]) (Tail3 o s u ++ recsL s ((o', u') :: l)))
        (hdR QN.WH0 (A ++ RecI 2 o s u ++ [1, 1]) (Tail3 o' s u' ++ recsL s l)) := by
      refine h1.of_eq ?_ ?_
      · simp [Tail3, recsL, Rec3_eq, List.append_assoc]
      · simp [RecI, List.append_assoc]
    have h2' : znttLogic.Reach
        (hdR QN.WH0 (A ++ RecI 2 o s u ++ [1, 1]) (Tail3 o' s u' ++ recsL s l))
        (hd QN.RZ0 (A ++ RecI 2 o s u ++ RecI 2 o' s u' ++ recsI s l) [0]) := h2
    refine h1'.trans (h2'.of_eq rfl ?_)
    simp [recsI, List.append_assoc]

end ZP.N
