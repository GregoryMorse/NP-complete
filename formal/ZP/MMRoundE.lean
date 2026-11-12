module

public import ZP.MMRows

@[expose] public section

/-! Rounds past the end of `A` (`a = 0`, `Mr` stays `M`): `roundE`, and `rowsRoundE` for the padded part of the last row. -/

namespace ZP.Mul.MM

open ZP

theorem roundE (Be Vt Xt Bd R0 : List Nat) (q : Nat) (v x : Nat)
    (hBe : Bits Be) (hVt : Bits Vt) (hXt : Bits Xt) (hBd : Bits Bd)
    (hv : v ∈ bits) (hx : x ∈ bits) (hlen : Vt.length = Xt.length) (hR : Sym4 R0) :
    zmmLogic.Reach
      (hdR QMM.RS1 (List.replicate q 1 ++ 1 :: (Be ++ Vt.reverse ++ [v]) ++ 0 :: Bd ++ [1])
        (0 :: (Xt.reverse ++ [x]) ++ 1 :: R0))
      (hdR QMM.RS1 (List.replicate q 1 ++ 1 :: Be ++ 0 :: (Vt.reverse ++ v :: Bd ++ [1]))
        (0 :: ((List.zipWith (jc 1) (v :: Vt) (x :: Xt)).reverse ++ [] ++ 1 :: R0))) := by
  have hBe4 := hBe.sym4
  have hVt4 := hVt.sym4
  have hBd4 := hBd.sym4
  have hXb : Bits (Xt.reverse ++ [x]) := fun c hc => by
    simp only [List.mem_append, List.mem_reverse, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact hXt c hc
    · exact hx
  have hVr : Bits Vt.reverse := fun c hc => hVt c (List.mem_reverse.mp hc)
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have h1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have hq : Sym4 (List.replicate q 1) := sym4_rep q 1 h1
  have hBr : Bits (Be ++ Vt.reverse) := fun c hc => by
    rcases List.mem_append.mp hc with hc | hc
    · exact hBe c hc
    · exact hVr c hc
  have hBr4 := hBr.sym4
  have hVr4 := hVr.sym4
  have hXb4 := hXb.sym4
  have hv4 : v ∈ ALL := by rcases mem_bits hv with rfl | rfl <;> simp [ALL]
  have hF0 : Sym4 (List.replicate q 1 ++ 1 :: (Be ++ Vt.reverse ++ [v])) := by
    simp [sym4_app_iff, sym4_cons_iff, *]
  have t0 := rsLoop (Xt.reverse ++ [x]) hXb
    (List.replicate q 1 ++ 1 :: (Be ++ Vt.reverse ++ [v]) ++ 0 :: Bd ++ [1])
    (by simp [sym4_app_iff, sym4_cons_iff, *]) R0 hR
  have t1 := toFA (List.replicate q 1 ++ 1 :: (Be ++ Vt.reverse ++ [v])) Bd
    (Xt.reverse ++ [x]) R0 hF0 hBd hXb hR
  have t2 := fetchE0 (Be ++ Vt.reverse) Bd (Xt.reverse ++ [x]) R0 v q hBr hv hBd hXb hR
  have e2 : List.replicate q 1 ++ 1 :: (Be ++ Vt.reverse ++ [v]) =
      (List.replicate q 1 ++ 1 :: (Be ++ Vt.reverse)) ++ [v] := by simp
  rw [e2, hd_snoc QMM.J1] at t2
  have t3 := bRow 1 (by simp) R0 hR Vt Xt hlen hVt hXt v x hv hx
    (List.replicate q 1 ++ 1 :: Be) Bd [] (by simp [sym4_app_iff, sym4_cons_iff, *]) hBd Bits.nil
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at t0 t1 t2 t3 ⊢
  exact t0.trans (t1.trans (t2.trans t3))

/-- `accFoldE Rws C`: the padded rounds with `a = 0` (symbol `1`). -/
def accFoldE : List (List Nat) → List Nat → List Nat
  | V :: Rws, C => accFoldE Rws (List.zipWith (jc 1) V C)
  | [], C => C

theorem rowsRoundE : ∀ (Rws : List (List Nat)) (C : List Nat), C ≠ [] → Bits C →
    (∀ r ∈ Rws, Bits r ∧ r.length = C.length) →
    ∀ (Be Bd R0 : List Nat) (q : Nat), Bits Be → Bits Bd → Sym4 R0 →
      zmmLogic.Reach
        (hdR QMM.RS1 (List.replicate q 1 ++ 1 :: (Be ++ stor Rws) ++ 0 :: Bd ++ [1]) (0 :: C.reverse ++ 1 :: R0))
        (hdR QMM.RS1 (List.replicate q 1 ++ 1 :: Be ++ 0 :: (stor Rws ++ Bd ++ [1]))
          (0 :: (accFoldE Rws C).reverse ++ 1 :: R0)) := by
  intro Rws
  induction Rws with
  | nil =>
    intro C _ _ _ Be Bd R0 q _ _ _
    simp [stor, accFoldE]
    exact LTM.Reach.refl _ _
  | cons V Rws ih =>
    intro C hCne hC hRws Be Bd R0 q hBe hBd hR0
    obtain ⟨hVb, hVl⟩ := hRws V (by simp)
    have hRws' : ∀ r ∈ Rws, Bits r ∧ r.length = C.length := fun r hr => hRws r (by simp [hr])
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
    have r1 := roundE (Be ++ stor Rws) Vt Xt Bd R0 q v x
      (fun c hc => by
        rcases List.mem_append.mp hc with hc | hc
        · exact hBe c hc
        · exact hst c hc)
      hVt hXt hBd hvb hxb hlen hR0
    have hC' : Bits (List.zipWith (jc 1) (v :: Vt) (x :: Xt)) := bits_zipWith _ _ _ hVb hC
    have hCne' : List.zipWith (jc 1) (v :: Vt) (x :: Xt) ≠ [] := by simp
    have hlC' := len_zipWith 1 (v :: Vt) (x :: Xt) hVl
    have r2 := ih _ hCne' hC' (fun r hr => ⟨(hRws' r hr).1, by rw [hlC']; exact (hRws' r hr).2⟩)
      Be ((v :: Vt).reverse ++ Bd) R0 q hBe (fun c hc => by
        rcases List.mem_append.mp hc with hc | hc
        · exact hVb c (List.mem_reverse.mp hc)
        · exact hBd c hc) hR0
    simp only [List.reverse_cons, stor, accFoldE, List.append_assoc,
      List.cons_append, List.nil_append] at r1 r2 ⊢
    exact r1.trans r2

end ZP.Mul.MM
