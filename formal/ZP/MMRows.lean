module

public import ZP.MMRound

@[expose] public section

/-! The `m` rounds of one row of `A` (`rowsRound`): the next `a` bits `As` (stored last-first, nearest the consumed `M`s) and
the next B rows `Rws` (stored `V.reverse`, the nearest to `P` first processed) are consumed; the accumulator
(column order) becomes `accFold`. -/

namespace ZP.Mul.MM

open ZP

def aOf (s : Nat) : Nat := if s = 2 then 1 else 0

def stor : List (List Nat) → List Nat
  | [] => []
  | V :: Rws => stor Rws ++ V.reverse

def accFold : List Nat → List (List Nat) → List Nat → List Nat
  | s :: As, V :: Rws, C => accFold As Rws (List.zipWith (jc (aOf s)) V C)
  | _, _, C => C

theorem bits_stor : ∀ (Rws : List (List Nat)), (∀ r ∈ Rws, Bits r) → Bits (stor Rws)
  | [], _ => Bits.nil
  | V :: Rws, h => by
    intro c hc
    simp only [stor, List.mem_append, List.mem_reverse] at hc
    rcases hc with hc | hc
    · exact bits_stor Rws (fun r hr => h r (by simp [hr])) c hc
    · exact h V (by simp) c hc

theorem bits_zipWith (a : Nat) (V C : List Nat) (hV : Bits V) (hC : Bits C) : Bits (List.zipWith (jc a) V C) := by
  induction V generalizing C with
  | nil => intro c hc; simp at hc
  | cons v V ih =>
    cases C with
    | nil => intro c hc; simp at hc
    | cons x C =>
      intro c hc
      simp only [List.zipWith_cons_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact jc_bits a v x (hC x (by simp))
      · exact ih C (fun b hb => hV b (by simp [hb])) (fun b hb => hC b (by simp [hb])) c hc

theorem len_zipWith (a : Nat) (V C : List Nat) (h : V.length = C.length) :
    (List.zipWith (jc a) V C).length = C.length := by
  simp [List.length_zipWith, h]

theorem rowsRound : ∀ (As : List Nat) (Rws : List (List Nat)), As.length = Rws.length →
    (∀ s ∈ As, s = 2 ∨ s = 3) → ∀ (C : List Nat), C ≠ [] → Bits C → (∀ r ∈ Rws, Bits r ∧ r.length = C.length) →
    ∀ (Au0 Be Bd R0 : List Nat) (q : Nat), Bits Au0 → Bits Be → Bits Bd → Sym4 R0 →
      zmmLogic.Reach
        (hdR QMM.RS1 (Au0 ++ As.reverse ++ List.replicate q 1 ++ 1 :: (Be ++ stor Rws) ++ 0 :: Bd ++ [1])
          (0 :: C.reverse ++ 1 :: R0))
        (hdR QMM.RS1 (Au0 ++ List.replicate (q + As.length) 1 ++ 1 :: Be ++ 0 :: (stor Rws ++ Bd ++ [1]))
          (0 :: (accFold As Rws C).reverse ++ 1 :: R0)) := by
  intro As
  induction As with
  | nil =>
    intro Rws hl _ C _ _ _ Au0 Be Bd R0 q _ _ _ _
    have : Rws = [] := List.length_eq_zero_iff.mp hl.symm
    subst this
    simp [stor, accFold]
    exact LTM.Reach.refl _ _
  | cons s As ih =>
    intro Rws hl hAs C hCne hC hRws Au0 Be Bd R0 q hAu0 hBe hBd hR0
    rcases Rws with _ | ⟨V, Rws⟩
    · simp at hl
    have hl' : As.length = Rws.length := by simpa using hl
    obtain ⟨hVb, hVl⟩ := hRws V (by simp)
    have hRws' : ∀ r ∈ Rws, Bits r ∧ r.length = C.length := fun r hr => hRws r (by simp [hr])
    have hAs' : ∀ t ∈ As, t = 2 ∨ t = 3 := fun t ht => hAs t (by simp [ht])
    have hs : s = 2 ∨ s = 3 := hAs s (by simp)
    have hAsb : Bits As := fun t ht => by rcases hAs' t ht with rfl | rfl <;> simp [bits]
    have hAsr : Bits As.reverse := fun t ht => hAsb t (List.mem_reverse.mp ht)
    obtain ⟨v, Vt, rfl⟩ : ∃ v Vt, V = v :: Vt := by
      cases V with
      | nil => exact absurd (by simpa using hVl.symm) hCne
      | cons v Vt => exact ⟨v, Vt, rfl⟩
    obtain ⟨x, Xt, rfl⟩ : ∃ x Xt, C = x :: Xt := by
      cases C with
      | nil => exact absurd rfl hCne
      | cons x Xt => exact ⟨x, Xt, rfl⟩
    have hvb : v ∈ bits := hVb v (by simp)
    have hVt : Bits Vt := fun c hc => hVb c (by simp [hc])
    have hxb : x ∈ bits := hC x (by simp)
    have hXt : Bits Xt := fun c hc => hC c (by simp [hc])
    have hlen : Vt.length = Xt.length := by simpa using hVl
    have hst : Bits (stor Rws) := bits_stor Rws (fun r hr => (hRws' r hr).1)
    have hsa : (s = 2 ∧ aOf s = 1) ∨ (s = 3 ∧ aOf s = 0) := by
      rcases hs with rfl | rfl <;> simp [aOf]
    have r1 := roundA s (aOf s) hsa (Au0 ++ As.reverse) (Be ++ stor Rws) Vt Xt (Bd) R0 q v x
      (fun c hc => by
        rcases List.mem_append.mp hc with hc | hc
        · exact hAu0 c hc
        · exact hAsr c hc)
      (fun c hc => by
        rcases List.mem_append.mp hc with hc | hc
        · exact hBe c hc
        · exact hst c hc)
      hVt hXt hBd hvb hxb hlen hR0
    have hC' : Bits (List.zipWith (jc (aOf s)) (v :: Vt) (x :: Xt)) := bits_zipWith _ _ _ hVb hC
    have hCne' : List.zipWith (jc (aOf s)) (v :: Vt) (x :: Xt) ≠ [] := by simp
    have hlC' := len_zipWith (aOf s) (v :: Vt) (x :: Xt) hVl
    have r2 := ih Rws hl' hAs' _ hCne' hC' (fun r hr => ⟨(hRws' r hr).1, by rw [hlC']; exact (hRws' r hr).2⟩)
      Au0 Be ((v :: Vt).reverse ++ Bd) R0 (q + 1) hAu0 hBe (fun c hc => by
        rcases List.mem_append.mp hc with hc | hc
        · exact hVb c (List.mem_reverse.mp hc)
        · exact hBd c hc) hR0
    have hq : q + (As.length + 1) = q + 1 + As.length := by omega
    simp only [List.reverse_cons, stor, accFold, List.length_cons, hq, List.replicate_succ, List.append_assoc,
      List.cons_append, List.nil_append, List.singleton_append] at r1 r2 ⊢
    exact r1.trans r2

end ZP.Mul.MM
