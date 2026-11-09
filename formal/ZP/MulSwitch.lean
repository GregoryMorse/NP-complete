module

public import ZP.MulInterp

@[expose] public section

/-! The switch of `native/zmul.py` as Lean lemmas, over `zmulLogic`. -/

namespace ZP.Mul

open ZP

/-- The insert state that carries the symbol `y` (`'0'` = 2, `'1'` = 3, `M` = 1). -/
def mQof (y : Nat) : Nat := if y = 1 then QMul.mQM else if y = 2 then QMul.mQ0 else QMul.mQ1

def ssets : Env := [ALL, NB]

theorem svalid {A Z : List Nat} (hA : Sym4 A) (hZ : NoB Z) : Valid ssets [A, Z] :=
  Valid.cons hA (Valid.cons hZ (Valid.nil _))

theorem qsBase (y : Nat) (hy : y ∈ NB) (A0 Z : List Nat) (hA : Sym4 A0) (hZ : NoB Z) :
    zmulLogic.Reach (hdR (mQof y) (A0 ++ 0 :: Z) []) (hdR QMul.mRX (A0 ++ [0]) (Z ++ [y])) := by
  have hv := svalid hA hZ
  have hy' : y = 1 ∨ y = 2 ∨ y = 3 := by simpa [NB] using hy
  rcases hy' with rfl | rfl | rfl
  · exact checkFF (env := [A0, Z]) (E := []) (k := 8) hv trivial
      (ls := [.blk 0 .id, .sym 0, .blk 1 .id]) (rs := [])
      (ls' := [.blk 0 .id, .sym 0]) (rs' := [.blk 1 .id, .sym 1])
      (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkFF (env := [A0, Z]) (E := []) (k := 8) hv trivial
      (ls := [.blk 0 .id, .sym 0, .blk 1 .id]) (rs := [])
      (ls' := [.blk 0 .id, .sym 0]) (rs' := [.blk 1 .id, .sym 2])
      (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkFF (env := [A0, Z]) (E := []) (k := 8) hv trivial
      (ls := [.blk 0 .id, .sym 0, .blk 1 .id]) (rs := [])
      (ls' := [.blk 0 .id, .sym 0]) (rs' := [.blk 1 .id, .sym 3])
      (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)


theorem qsStep (y c : Nat) (hy : y ∈ NB) (hc : c ∈ NB) (A0 Z ST : List Nat) (hA : Sym4 A0)
    (hZ : NoB Z) (hS : NoB ST) :
    zmulLogic.Reach (hdR (mQof y) (A0 ++ 0 :: Z) (c :: ST))
      (hdR (mQof c) (A0 ++ 0 :: (Z ++ [y])) ST) := by
  have hv : Valid [ALL, NB, NB] [A0, Z, ST] :=
    Valid.cons hA (Valid.cons hZ (Valid.cons hS (Valid.nil _)))
  have hy' : y = 1 ∨ y = 2 ∨ y = 3 := by simpa [NB] using hy
  have hc' : c = 1 ∨ c = 2 ∨ c = 3 := by simpa [NB] using hc
  rcases hy' with rfl | rfl | rfl <;> rcases hc' with rfl | rfl | rfl <;>
  first
    | exact checkFF (env := [A0, Z, ST]) (E := []) (k := 6) hv trivial
        (ls := [.blk 0 .id, .sym 0, .blk 1 .id]) (rs := [.sym 1, .blk 2 .id])
        (ls' := [.blk 0 .id, .sym 0, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
    | exact checkFF (env := [A0, Z, ST]) (E := []) (k := 6) hv trivial
        (ls := [.blk 0 .id, .sym 0, .blk 1 .id]) (rs := [.sym 2, .blk 2 .id])
        (ls' := [.blk 0 .id, .sym 0, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
    | exact checkFF (env := [A0, Z, ST]) (E := []) (k := 6) hv trivial
        (ls := [.blk 0 .id, .sym 0, .blk 1 .id]) (rs := [.sym 3, .blk 2 .id])
        (ls' := [.blk 0 .id, .sym 0, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
    | exact checkFF (env := [A0, Z, ST]) (E := []) (k := 6) hv trivial
        (ls := [.blk 0 .id, .sym 0, .blk 1 .id]) (rs := [.sym 1, .blk 2 .id])
        (ls' := [.blk 0 .id, .sym 0, .blk 1 .id, .sym 2]) (rs' := [.blk 2 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
    | exact checkFF (env := [A0, Z, ST]) (E := []) (k := 6) hv trivial
        (ls := [.blk 0 .id, .sym 0, .blk 1 .id]) (rs := [.sym 2, .blk 2 .id])
        (ls' := [.blk 0 .id, .sym 0, .blk 1 .id, .sym 2]) (rs' := [.blk 2 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
    | exact checkFF (env := [A0, Z, ST]) (E := []) (k := 6) hv trivial
        (ls := [.blk 0 .id, .sym 0, .blk 1 .id]) (rs := [.sym 3, .blk 2 .id])
        (ls' := [.blk 0 .id, .sym 0, .blk 1 .id, .sym 2]) (rs' := [.blk 2 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
    | exact checkFF (env := [A0, Z, ST]) (E := []) (k := 6) hv trivial
        (ls := [.blk 0 .id, .sym 0, .blk 1 .id]) (rs := [.sym 1, .blk 2 .id])
        (ls' := [.blk 0 .id, .sym 0, .blk 1 .id, .sym 3]) (rs' := [.blk 2 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
    | exact checkFF (env := [A0, Z, ST]) (E := []) (k := 6) hv trivial
        (ls := [.blk 0 .id, .sym 0, .blk 1 .id]) (rs := [.sym 2, .blk 2 .id])
        (ls' := [.blk 0 .id, .sym 0, .blk 1 .id, .sym 3]) (rs' := [.blk 2 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
    | exact checkFF (env := [A0, Z, ST]) (E := []) (k := 6) hv trivial
        (ls := [.blk 0 .id, .sym 0, .blk 1 .id]) (rs := [.sym 3, .blk 2 .id])
        (ls' := [.blk 0 .id, .sym 0, .blk 1 .id, .sym 3]) (rs' := [.blk 2 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)

/-- Insert `y` at the front of the storage text `ST`; the head comes back to the front. -/
theorem qs (ST : List Nat) (hS : NoB ST) : ∀ (y : Nat), y ∈ NB → ∀ (A0 Z : List Nat),
    Sym4 A0 → NoB Z →
    zmulLogic.Reach (hdR (mQof y) (A0 ++ 0 :: Z) ST) (hdR QMul.mRX (A0 ++ [0]) (Z ++ y :: ST)) := by
  induction ST with
  | nil =>
    intro y hy A0 Z hA hZ
    exact qsBase y hy A0 Z hA hZ
  | cons c ST ih =>
    intro y hy A0 Z hA hZ
    have hc : c ∈ NB := hS c (List.mem_cons_self ..)
    have hS' : NoB ST := fun a ha => hS a (List.mem_cons_of_mem _ ha)
    have h1 := qsStep y c hy hc A0 Z ST hA hZ hS'
    have h2 := ih hS' c hc A0 (Z ++ [y]) hA (hZ.app (fun a ha => by
      rw [List.mem_singleton.mp ha]; exact hy))
    rw [List.append_assoc] at h2
    exact h1.trans h2

/-- Stage 1 of one shift iteration: take the leftmost cell `a` of the guest cells, blank it and
sweep to the separator. -/
theorem sw1 (a : Nat) (ha : a = 2 ∨ a = 3) (P N ST : List Nat) (hP : Sym4 P) (hN : NoB N)
    (hS : NoB ST) :
    zmulLogic.Reach (hdR QMul.mTK (P ++ [0]) (a :: N ++ 0 :: ST))
      (hdR (mQof a) (P ++ [0, 0] ++ N ++ [0]) ST) := by
  have hv : Valid [ALL, NB, NB] [P, N, ST] :=
    Valid.cons hP (Valid.cons hN (Valid.cons hS (Valid.nil _)))
  rcases ha with rfl | rfl
  · exact checkFF (env := [P, N, ST]) (E := []) (k := 6) hv trivial
      (ls := [.blk 0 .id, .sym 0]) (rs := [.sym 2, .blk 1 .id, .sym 0, .blk 2 .id])
      (ls' := [.blk 0 .id, .sym 0, .sym 0, .blk 1 .id, .sym 0]) (rs' := [.blk 2 .id])
      (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkFF (env := [P, N, ST]) (E := []) (k := 6) hv trivial
      (ls := [.blk 0 .id, .sym 0]) (rs := [.sym 3, .blk 1 .id, .sym 0, .blk 2 .id])
      (ls' := [.blk 0 .id, .sym 0, .sym 0, .blk 1 .id, .sym 0]) (rs' := [.blk 2 .id])
      (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)

/-- Stage 3: come back from the separator to the leftmost remaining cell. -/
theorem sw3 (y : Nat) (hy : y ∈ NB) (P N ST : List Nat) (hP : Sym4 P) (hN : NoB N) (hS : NoB ST)
    (hy2 : y = 2 ∨ y = 3) :
    zmulLogic.Reach (hdR QMul.mRX (P ++ [0, 0] ++ N ++ [0]) (y :: ST))
      (hdR QMul.mTK (P ++ [0, 0]) (N ++ 0 :: y :: ST)) := by
  have hv : Valid [ALL, NB, NB] [P, N, ST] :=
    Valid.cons hP (Valid.cons hN (Valid.cons hS (Valid.nil _)))
  rcases hy2 with rfl | rfl
  · exact checkFF (env := [P, N, ST]) (E := []) (k := 6) hv trivial
      (ls := [.blk 0 .id, .sym 0, .sym 0, .blk 1 .id, .sym 0]) (rs := [.sym 2, .blk 2 .id])
      (ls' := [.blk 0 .id, .sym 0, .sym 0]) (rs' := [.blk 1 .id, .sym 0, .sym 2, .blk 2 .id])
      (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkFF (env := [P, N, ST]) (E := []) (k := 6) hv trivial
      (ls := [.blk 0 .id, .sym 0, .sym 0, .blk 1 .id, .sym 0]) (rs := [.sym 3, .blk 2 .id])
      (ls' := [.blk 0 .id, .sym 0, .sym 0]) (rs' := [.blk 1 .id, .sym 0, .sym 3, .blk 2 .id])
      (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)

theorem swIter (a : Nat) (ha : a = 2 ∨ a = 3) (P N ST : List Nat) (hP : Sym4 P) (hN : NoB N)
    (hS : NoB ST) :
    zmulLogic.Reach (hdR QMul.mTK (P ++ [0]) (a :: N ++ 0 :: ST))
      (hdR QMul.mTK (P ++ [0, 0]) (N ++ 0 :: a :: ST)) := by
  have haNB : a ∈ NB := by rcases ha with rfl | rfl <;> simp [NB]
  have hA : Sym4 (P ++ [0, 0] ++ N) := by
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (hx | rfl | rfl) | hx
    · exact hP x hx
    · simp [ALL]
    · simp [ALL]
    · have := hN x hx; simp [NB, ALL] at *; omega
  have hmQ : mQof a = mQof a := rfl
  have h1 := sw1 a ha P N ST hP hN hS
  have h2 := qs ST hS a haNB (P ++ [0, 0] ++ N) [] hA NoB.nil
  have h3 := sw3 a haNB P N ST hP hN hS ha
  simp only [List.nil_append] at h2
  exact h1.trans (h2.trans h3)

theorem swLoop (Lw : List Nat) (hL : ∀ a ∈ Lw, a = 2 ∨ a = 3) (Zf : List Nat) (hZ : NoB Zf) :
    ∀ (P ST : List Nat), Sym4 P → NoB ST →
    zmulLogic.Reach (hdR QMul.mTK (P ++ [0]) (Lw ++ 1 :: Zf ++ 0 :: ST))
      (hdR QMul.mTK (P ++ List.replicate (Lw.length + 1) 0) (1 :: Zf ++ 0 :: (Lw.reverse ++ ST))) := by
  induction Lw with
  | nil => intro P ST hP hS; simpa using LTM.Reach.refl _ _
  | cons a Lw ih =>
    intro P ST hP hS
    have ha := hL a (List.mem_cons_self ..)
    have hL' : ∀ b ∈ Lw, b = 2 ∨ b = 3 := fun b hb => hL b (List.mem_cons_of_mem _ hb)
    have hN : NoB (Lw ++ 1 :: Zf) := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · have := hL' x hx; rcases this with rfl | rfl <;> simp [NB]
      · rcases List.mem_cons.mp hx with rfl | hx
        · simp [NB]
        · exact hZ x hx
    have h1 := swIter a ha P (Lw ++ 1 :: Zf) ST hP hN hS
    have hP' : Sym4 (P ++ [0]) := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hP x hx
      · simp at hx; subst hx; simp [ALL]
    have haNB : a ∈ NB := by rcases ha with rfl | rfl <;> simp [NB]
    have hS' : NoB (a :: ST) := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact haNB
      · exact hS x hx
    have h2 := ih hL' (P ++ [0]) (a :: ST) hP' hS'
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 ⊢
    have e : P ++ (0 :: List.replicate (Lw.length + 1) 0) = P ++ 0 :: 0 :: List.replicate Lw.length 0 := by
      simp [List.replicate_succ]
    rw [List.length_cons, List.replicate_succ, List.reverse_cons, List.append_assoc]
    simp only [List.singleton_append]
    exact h1.trans (by simpa [List.replicate_succ] using h2)

/-! ## Terminator and pop -/

theorem term1 (P1 Zf ST : List Nat) (hP : Sym4 P1) (hZ : NoB Zf) (hS : NoB ST) :
    zmulLogic.Reach (hdR QMul.mTK P1 (1 :: Zf ++ 0 :: ST))
      (hdR QMul.mQM (P1 ++ 0 :: Zf ++ [0]) ST) := by
  have hv : Valid [ALL, NB, NB] [P1, Zf, ST] :=
    Valid.cons hP (Valid.cons hZ (Valid.cons hS (Valid.nil _)))
  exact checkFF (env := [P1, Zf, ST]) (E := []) (k := 6) hv trivial
      (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id, .sym 0, .blk 2 .id])
      (ls' := [.blk 0 .id, .sym 0, .blk 1 .id, .sym 0]) (rs' := [.blk 2 .id])
      (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)

theorem term2 (B ST : List Nat) (hB : Sym4 B) (hS : NoB ST) :
    zmulLogic.Reach (hdR QMul.mRX (B ++ [0]) (1 :: ST))
      (hdR QMul.mPB0 (B ++ [0, 1]) ST) := by
  have hv := svalid hB hS
  exact checkFF (env := [B, ST]) (E := []) (k := 6) hv trivial
      (ls := [.blk 0 .id, .sym 0]) (rs := [.sym 1, .blk 1 .id])
      (ls' := [.blk 0 .id, .sym 0, .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)

def psets : Env := [ALL, ALL, NB, NB, NB]

theorem popStep (x : Nat) (hx : x = 2 ∨ x = 3) (Pre : List Nat) (r : Nat) (D U V : List Nat)
    (hP : Sym4 Pre) (hD : NoB D) (hU : NoB U) (hV : NoB V) :
    zmulLogic.Reach
      (hdR QMul.mPB0 (Pre ++ List.replicate (r + 1) 0 ++ D ++ [0] ++ U) (V ++ [x]))
      (hdR QMul.mPB0 (Pre ++ List.replicate r 0 ++ x :: D ++ [0]) (U ++ V)) := by
  have hv : Valid psets [Pre, List.replicate r 0, D, U, V] :=
    Valid.cons hP (Valid.cons (zeros4 r) (Valid.cons hD (Valid.cons hU (Valid.cons hV (Valid.nil _)))))
  rw [List.replicate_succ']
  rcases hx with rfl | rfl
  · exact checkFF (env := [Pre, List.replicate r 0, D, U, V]) (E := []) (k := 40) hv trivial
      (ls := [.blk 0 .id, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0, .blk 3 .id])
      (rs := [.blk 4 .id, .sym 2])
      (ls' := [.blk 0 .id, .blk 1 (.const 0), .sym 2, .blk 2 .id, .sym 0]) (rs' := [.blk 3 .id, .blk 4 .id])
      (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkFF (env := [Pre, List.replicate r 0, D, U, V]) (E := []) (k := 40) hv trivial
      (ls := [.blk 0 .id, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0, .blk 3 .id])
      (rs := [.blk 4 .id, .sym 3])
      (ls' := [.blk 0 .id, .blk 1 (.const 0), .sym 3, .blk 2 .id, .sym 0]) (rs' := [.blk 3 .id, .blk 4 .id])
      (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)

theorem pbSweep (A V : List Nat) (hA : Sym4 A) (hV : NoB V) :
    zmulLogic.Reach (hdR QMul.mPB0 A (V ++ [1])) (hd QMul.mPB (A ++ V ++ [1]) []) := by
  have hv := svalid hA hV
  exact checkFT (env := [A, V]) (E := []) (k := 8) hv trivial
      (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [])
      (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)

theorem popLoop (Fr : List Nat) (hF : Bits Fr) : ∀ (Pre : List Nat) (r : Nat) (D U V : List Nat),
    Fr.length ≤ r → Sym4 Pre → NoB D → NoB U → NoB V →
    zmulLogic.Reach (hdR QMul.mPB0 (Pre ++ List.replicate r 0 ++ D ++ [0] ++ U) (V ++ 1 :: Fr.reverse))
      (hd QMul.mPB (Pre ++ List.replicate (r - Fr.length) 0 ++ Fr.reverse ++ D ++ [0] ++ U ++ V ++ [1]) []) := by
  induction Fr with
  | nil =>
    intro Pre r D U V _ hP hD hU hV
    have := pbSweep (Pre ++ List.replicate r 0 ++ D ++ [0] ++ U) V
      (((((hP.app (zeros4 r)).app hD.sym4).app (Sym4.cons (by simp [ALL]) Sym4.nil)).app hU.sym4)) hV
    simpa using this
  | cons x Fr ih =>
    intro Pre r D U V hr hP hD hU hV
    have hx : x ∈ bits := hF x (List.mem_cons_self ..)
    have hF' : Bits Fr := fun a ha => hF a (List.mem_cons_of_mem _ ha)
    have hxNB : x ∈ NB := by rcases mem_bits hx with rfl | rfl <;> simp [NB]
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by simp at hr; omega⟩
    have hV' : NoB (V ++ 1 :: Fr.reverse) := by
      refine hV.app (fun a ha => ?_)
      rcases List.mem_cons.mp ha with rfl | ha
      · simp [NB]
      · have := hF' a (List.mem_reverse.mp ha)
        rcases mem_bits this with rfl | rfl <;> simp [NB]
    have h1 := popStep x (mem_bits hx) Pre r' D U (V ++ 1 :: Fr.reverse) hP hD hU hV'
    have hD' : NoB (x :: D) := by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hxNB
      · exact hD a ha
    have h2 := ih hF' Pre r' (x :: D) [] (U ++ V) (by simp at hr; omega) hP hD'
      NoB.nil (hU.app hV)
    have e : V ++ 1 :: (x :: Fr).reverse = (V ++ 1 :: Fr.reverse) ++ [x] := by simp
    rw [e]
    have e2 : U ++ (V ++ 1 :: Fr.reverse) = (U ++ V) ++ 1 :: Fr.reverse := by simp
    rw [e2] at h1
    rw [List.append_nil] at h2
    have h3 := h1.trans h2
    simpa [List.reverse_cons, List.append_assoc] using h3

theorem popEnd (Pre : List Nat) (n : Nat) (D T : List Nat) (hP : Sym4 Pre) (hD : NoB D) (hT : NoB T) :
    zmulLogic.Reach
      (hd QMul.mPB (Pre ++ List.replicate (n + 1) 0 ++ D ++ [0] ++ T ++ [1]) [])
      (hd Q.RTW (Pre ++ List.replicate n 0) (0 :: D ++ 0 :: T ++ [0])) := by
  have hv : Valid [ALL, ALL, NB, NB] [Pre, List.replicate n 0, D, T] :=
    Valid.cons hP (Valid.cons (zeros4 n) (Valid.cons hD (Valid.cons hT (Valid.nil _))))
  rw [List.replicate_succ']
  exact checkTT (env := [Pre, List.replicate n 0, D, T]) (E := []) (k := 12) hv trivial
      (ls := [.blk 0 .id, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0, .blk 3 .id, .sym 1])
      (rs := [])
      (ls' := [.blk 0 .id, .blk 1 (.const 0)])
      (rs' := [.sym 0, .blk 2 .id, .sym 0, .blk 3 .id, .sym 0])
      (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)

theorem Sym4.zero : Sym4 [0] := Sym4.cons (by simp [ALL]) Sym4.nil

theorem Bits.two (hL : Bits Lw) : ∀ a ∈ Lw, a = 2 ∨ a = 3 := fun a ha => mem_bits (hL a ha)

theorem switchCore (Qc Lw Zf ST0 F : List Nat) (g : Nat) (hQ : Sym4 Qc) (hL : Bits Lw)
    (hZ : NoB Zf) (hS0 : NoB ST0) (hF : Bits F) (hcap : F.length ≤ g + Lw.length + 1) :
    zmulLogic.Reach
      (hdR QMul.mTK (Qc ++ List.replicate (g + 1) 0) (Lw ++ 1 :: Zf ++ 0 :: (ST0 ++ 1 :: F)))
      (hd Q.RTW (Qc ++ List.replicate (g + Lw.length + 1 - F.length) 0)
        (0 :: (F ++ Zf) ++ 0 :: 1 :: ((Lw.reverse ++ ST0) ++ [0]))) := by
  have hNBF : NoB F := hF.noB
  have hNBL : NoB Lw := hL.noB
  have hS : NoB (ST0 ++ 1 :: F) := hS0.app (fun a ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · simp [NB]
    · exact hNBF a ha)
  have hP : Sym4 (Qc ++ List.replicate g 0) := hQ.app (zeros4 g)
  have h1 := swLoop Lw hL.two Zf hZ (Qc ++ List.replicate g 0) (ST0 ++ 1 :: F) hP hS
  rw [List.append_assoc, ← List.replicate_succ'] at h1
  -- terminator
  have hNBLr : NoB Lw.reverse := fun a ha => hNBL a (List.mem_reverse.mp ha)
  have hrev : NoB (Lw.reverse ++ (ST0 ++ 1 :: F)) := hNBLr.app hS
  have hP1 : Sym4 (Qc ++ (List.replicate g 0 ++ List.replicate (Lw.length + 1) 0)) := by
    rw [← List.append_assoc]; exact (hP.app (zeros4 _))
  have h2 := term1 (Qc ++ (List.replicate g 0 ++ List.replicate (Lw.length + 1) 0)) Zf
    (Lw.reverse ++ (ST0 ++ 1 :: F)) hP1 hZ hrev
  have hA0 : Sym4 (Qc ++ (List.replicate g 0 ++ List.replicate (Lw.length + 1) 0) ++ [0] ++ Zf) :=
    ((hP1.app Sym4.zero).app hZ.sym4)
  have h3 := qs (Lw.reverse ++ (ST0 ++ 1 :: F)) hrev 1 (by simp [NB]) _ [] hA0 NoB.nil
  have h4 := term2 (Qc ++ (List.replicate g 0 ++ List.replicate (Lw.length + 1) 0) ++ [0] ++ Zf)
    (Lw.reverse ++ (ST0 ++ 1 :: F)) hA0 hrev
  have hFr : Bits F.reverse := fun a ha => hF a (List.mem_reverse.mp ha)
  have hV : NoB (Lw.reverse ++ ST0) := hNBLr.app hS0
  have h5 := popLoop F.reverse hFr Qc (g + Lw.length + 2) Zf [1] (Lw.reverse ++ ST0)
    (by simp; omega) hQ hZ (by intro a ha; simp at ha; subst ha; simp [NB]) hV
  have h6 := popEnd Qc (g + Lw.length + 1 - F.length) (F ++ Zf) (1 :: (Lw.reverse ++ ST0)) hQ
    (hNBF.app hZ) (fun a ha => by
      rcases List.mem_cons.mp ha with rfl | ha
      · simp [NB]
      · exact hV a ha)
  have er : List.replicate (g + Lw.length + 2) 0
      = List.replicate g 0 ++ List.replicate (Lw.length + 1) 0 ++ [0] := by
    rw [show g + Lw.length + 2 = g + (Lw.length + 1) + 1 by omega, List.replicate_succ',
      ← List.replicate_append_replicate]
  have en : g + Lw.length + 1 - F.length + 1 = g + Lw.length + 2 - F.length := by omega
  rw [en] at h6
  rw [er] at h5
  simp only [List.reverse_reverse, List.length_reverse] at h5
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at h1 h2 h3 h4 h5 h6 ⊢
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))

/-! ## The switch peek -/

def swsets : Env := [bits, ALL, bits, bits, NB, NB, NB]

theorem segSw (Qw Lw Rw W Fw ST : List Nat) (g w : Nat) (hw : w = 2 ∨ w = 3)
    (hQ : Bits Qw) (hL : Bits Lw) (hR : Bits Rw) (hW : NoB W) (hFw : NoB Fw) (hS : NoB ST) :
    zmulLogic.Reach
      (hd Q.FBACK (Qw ++ [2, 3, w] ++ List.replicate g 0 ++ 0 :: (Lw ++ [0]))
        (1 :: (Rw ++ 1 :: W ++ 1 :: Fw ++ 0 :: ST)))
      (hdR QMul.mTK (Qw ++ [2, 3, w] ++ List.replicate (g + 1) 0)
        (Lw ++ 1 :: (1 :: (Rw ++ 1 :: W ++ 1 :: Fw)) ++ 0 :: ST)) := by
  have hv : Valid swsets [Qw, List.replicate g 0, Lw, Rw, W, Fw, ST] :=
    Valid.cons hQ (Valid.cons (zeros4 g) (Valid.cons hL (Valid.cons hR (Valid.cons hW
      (Valid.cons hFw (Valid.cons hS (Valid.nil _)))))))
  rw [List.replicate_succ']
  rcases hw with rfl | rfl
  · exact checkTF (env := [Qw, List.replicate g 0, Lw, Rw, W, Fw, ST]) (E := []) (k := 60) hv trivial
      (ls := [.blk 0 .id, .sym 2, .sym 3, .sym 2, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0])
      (rs := [.sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id, .sym 0, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 2, .sym 3, .sym 2, .blk 1 (.const 0), .sym 0])
      (rs' := [.blk 2 .id, .sym 1, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id, .sym 0, .blk 6 .id])
      (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkTF (env := [Qw, List.replicate g 0, Lw, Rw, W, Fw, ST]) (E := []) (k := 60) hv trivial
      (ls := [.blk 0 .id, .sym 2, .sym 3, .sym 3, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0])
      (rs := [.sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id, .sym 0, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 2, .sym 3, .sym 3, .blk 1 (.const 0), .sym 0])
      (rs' := [.blk 2 .id, .sym 1, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id, .sym 0, .blk 6 .id])
      (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)

end ZP.Mul
