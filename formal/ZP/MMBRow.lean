module

public import ZP.MMJ
public import ZP.MMRBLoop

@[expose] public section

/-! One B row of the check phase: `n` j-steps (`jMore` ... `jLast`), accumulator updated by `jc`. -/

namespace ZP.Mul.MM

open ZP

theorem jc_bits (a v x : Nat) (hx : x ∈ bits) : jc a v x ∈ bits := by
  rcases mem_bits hx with rfl | rfl <;> by_cases h : a = 0 ∧ v = 3 <;> simp [jc, h, bits]

theorem bRow (a : Nat) (ha : a = 1 ∨ a = 0) (Tl : List Nat) (hTl : Sym4 Tl) :
    ∀ (Vt Xt : List Nat), Vt.length = Xt.length → Bits Vt → Bits Xt →
    ∀ (v x : Nat), v ∈ bits → x ∈ bits → ∀ (F0 Bp ALr : List Nat), Sym4 F0 → Bits Bp → Bits ALr →
      zmmLogic.Reach
        (hdR QMM.J1 (F0 ++ Vt.reverse)
          (v :: 0 :: (Bp ++ a :: (Xt.reverse ++ [x] ++ 0 :: (ALr ++ 1 :: Tl)))))
        (hdR QMM.RS1 (F0 ++ 0 :: (Vt.reverse ++ v :: Bp ++ [1]))
          (0 :: ((List.zipWith (jc a) (v :: Vt) (x :: Xt)).reverse ++ ALr ++ 1 :: Tl))) := by
  intro Vt
  induction Vt with
  | nil =>
    intro Xt hl hVt hXt v x hv hx F0 Bp ALr hF hBp hAL
    have : Xt = [] := List.length_eq_zero_iff.mp hl.symm
    subst this
    have := jLast Tl ALr Bp F0 a v x hTl hAL hBp hF ha hv hx
    simpa [List.zipWith] using this
  | cons v2 Vt ih =>
    intro Xt hl hVt hXt v x hv hx F0 Bp ALr hF hBp hAL
    rcases Xt with _ | ⟨y, Xt⟩
    · simp at hl
    have hl' : Vt.length = Xt.length := by simpa using hl
    have hv2 : v2 ∈ bits := hVt v2 (by simp)
    have hy : y ∈ bits := hXt y (by simp)
    have hVt' : Bits Vt := fun b hb => hVt b (by simp [hb])
    have hXt' : Bits Xt := fun b hb => hXt b (by simp [hb])
    have hXr : Bits Xt.reverse := fun b hb => hXt' b (by simpa using hb)
    have hFr : Sym4 (F0 ++ (Vt.reverse ++ [v2])) :=
      Sym4.app hF (Sym4.app (fun b hb => hVt'.sym4 b (by simpa using hb)) (Sym4.cons (by rcases mem_bits hv2 with rfl | rfl <;> simp [ALL]) Sym4.nil))
    have hs := jMore Tl ALr (Xt.reverse) Bp (F0 ++ (Vt.reverse ++ [v2])) a v x y hTl hAL hXr hBp hFr ha hv hx hy
    have e2 : F0 ++ (Vt.reverse ++ [v2]) = (F0 ++ Vt.reverse) ++ [v2] := by simp
    rw [e2, hd_snoc] at hs
    have hF' : Sym4 (F0 ++ Vt.reverse) :=
      Sym4.app hF (fun b hb => hVt'.sym4 b (by simpa using hb))
    have hBp' : Bits (v :: Bp) := Bits.cons hv hBp
    have hAL' : Bits (jc a v x :: ALr) := Bits.cons (jc_bits a v x hx) hAL
    have hr := ih Xt hl' hVt' hXt' v2 y hv2 hy F0 (v :: Bp) (jc a v x :: ALr) hF hBp' hAL'
    simp only [List.cons_append, List.append_assoc, List.nil_append, List.singleton_append] at hs hr
    simp only [List.zipWith, List.reverse_cons, List.cons_append, List.append_assoc, List.nil_append, List.singleton_append] at hr ⊢
    exact hs.trans hr

end ZP.Mul.MM
