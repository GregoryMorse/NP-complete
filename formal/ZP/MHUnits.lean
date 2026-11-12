module

public import ZP.MHUnitSeg

@[expose] public section

/-!
# Multihead units (shared by `Z_LP` and `Z_LNL`)

Appending units to the storage and the walker that appends one unit per step of the walk back through
the decider code. The tape between runs is

    B Jl M Jr M s M Mid B S           (the walker is the first `M`; `B` right of `Mid` separates the storage)

with `s = bitsOf x` and the storage `S = ustoreN x k`: `k` units, all heads at position 0, the last one current
(`M B x 0`), the others `M M x 0`.
-/

namespace ZP

theorem LTM.Reach.trans_eq {M : LTM} {a b c d : ZC} (h1 : M.Reach a b) (e : b = c) (h2 : M.Reach c d) :
    M.Reach a d := by
  subst e
  exact h1.trans h2

end ZP

namespace ZP.MH

open ZP

theorem hdR_eq' (q : Nat) (A R : List Nat) :
    hdR q A R = ⟨q, sapp A.reverse blank, sapp R blank⟩ := by
  show (⟨q, sapp (dL [A, R] [.blk 0 .id]) blank, sapp (dR [A, R] [.blk 1 .id]) blank⟩ : ZC) = _
  rw [dW_blk0, dW_blk1]

theorem hd_eq' (q : Nat) (A R : List Nat) :
    hd q A R = ⟨q, stail (sapp A.reverse blank), scons (sapp A.reverse blank 0) (sapp R blank)⟩ := by
  show (⟨q, stail (sapp (dL [A, R] [.blk 0 .id]) blank),
    scons (sapp (dL [A, R] [.blk 0 .id]) blank 0) (sapp (dR [A, R] [.blk 1 .id]) blank)⟩ : ZC) = _
  rw [dW_blk0, dW_blk1]

theorem sapp_lead0 (A : List Nat) : sapp (A ++ [0]) blank = sapp A blank := by
  rw [sapp_append]
  show sapp A (scons 0 blank) = _
  rw [scons_blank]

/-- A blank cell at the far left changes nothing. -/
theorem hdR_lead0 (q : Nat) (A R : List Nat) : hdR q (0 :: A) R = hdR q A R := by
  rw [hdR_eq', hdR_eq', List.reverse_cons, sapp_lead0]

theorem hd_lead0 (q : Nat) (A R : List Nat) (hA : A ≠ []) : hd q (0 :: A) R = hd q A R := by
  rw [hd_eq', hd_eq', List.reverse_cons, sapp_lead0]

/-! ## The storage of the unit chain -/

/-- `k` units, all heads at position 0, the last unit current. -/
def ustoreN (x : List Bool) : Nat → List Nat
  | 0 => []
  | j + 1 => ucs (uOf x) (List.replicate j 0) ++ uc (uOf x) 0 0

theorem ustoreN_zero (x : List Bool) : ustoreN x 0 = [] := rfl

theorem ustoreN_succ (x : List Bool) (j : Nat) :
    ustoreN x (j + 1) = ucs (uOf x) (List.replicate j 0) ++ uc (uOf x) 0 0 := rfl

theorem ustoreN_one (x : List Bool) : ustoreN x 1 = 1 :: 0 :: uOf x := by
  simp [ustoreN, uc]

theorem ustoreN_eq (x : List Bool) (j : Nat) :
    ustoreN x (j + 1) = storeOf x (List.replicate (j + 1) 0) 0 := by
  simp [ustoreN, storeOf, cfg, List.replicate_succ]

theorem uOf_cons (x : List Bool) : ∃ c u2, uOf x = c :: u2 ∧ c ∈ bits ∧ Bits u2 := by
  cases x with
  | nil => exact ⟨2, [], rfl, by simp [bits], Bits.nil⟩
  | cons b t =>
    refine ⟨bn b, bitsOf t ++ [2], by simp [uOf, bitsOf, bn], bn_bits b, ?_⟩
    exact (Bits.ofB t).app (fun a ha => by simp at ha; subst ha; simp [bits])

theorem ucs_noB (x : List Bool) (ps : List Nat) : NoB (ucs (uOf x) ps) := NoB.ucs (Bits.uOf x) ps

/-- Copy loop of the unit append. -/
theorem uLoop (Jl Jr Mid Sx : List Nat) (hJl : Bits Jl) (hJr : Bits Jr) (hMid : NoB Mid) (hSx : NoB Sx) :
    ∀ (v u w : List Nat), Bits v → Bits u → Bits w →
      mhBase.Reach
        (hdR QMH.UCP ([0] ++ Jl ++ [1] ++ Jr ++ [1] ++ u) (v ++ [1] ++ Mid ++ [0] ++ Sx ++ [1, 1] ++ w))
        (hdR QMH.UCP ([0] ++ Jl ++ [1] ++ Jr ++ [1] ++ (u ++ v)) ([1] ++ Mid ++ [0] ++ Sx ++ [1, 1] ++ (w ++ v)))
  | [], u, w, _, _, _ => by
    simp only [List.append_nil, List.nil_append]
    exact LTM.Reach.refl _ _
  | b :: v, u, w, hv, hu, hw => by
    have h1 := uBody Jl Jr u v Mid Sx w b hv.head hJl hJr hu hv.tail hMid hSx hw
    have h2 := uLoop Jl Jr Mid Sx hJl hJr hMid hSx v (u ++ [b]) (w ++ [b]) hv.tail (hu.snoc hv.head)
      (hw.snoc hv.head)
    exact h1.trans_eq (hdR_eq (by simp) (by simp)) (h2.ofEq rfl (hdR_eq (by simp) (by simp)))

/-- One unit appended. -/
theorem unitApp (x : List Bool) (Jl Jr Mid L Rt : List Nat) (hJl : Bits Jl) (hJr : Bits Jr) (hMid : NoB Mid)
    (hL : Sym4 L) (hRt : NoB Rt) (hLR : L ++ Rt = Jl ++ 1 :: (Jr ++ 1 :: (bitsOf x ++ 1 :: Mid))) (k : Nat) :
    mhBase.Reach (hdR QMH.U0 L (Rt ++ 0 :: ustoreN x k))
      (hdR QMH.UDW [0] (Jl ++ 1 :: (Jr ++ 1 :: (bitsOf x ++ 1 :: (Mid ++ 0 :: ustoreN x (k + 1)))))) := by
  have hs : Bits (bitsOf x) := Bits.ofB x
  cases k with
  | zero =>
    have h1 := uA1e L Rt hL hRt
    have h2 := uA2 Jl Jr (bitsOf x) Mid [] hJl hJr hs hMid NoB.nil
    have h3 := uLoop Jl Jr Mid [] hJl hJr hMid NoB.nil (bitsOf x) [] [] hs Bits.nil Bits.nil
    have h4 := uEnd Jl Jr (bitsOf x) Mid [] (bitsOf x) hJl hJr hs hMid NoB.nil hs
    have h5 := (h1.trans_eq (hd_eq (by rw [hLR] <;> simp) rfl) (h2.trans_eq (hdR_eq (by simp) (by simp))
      (h3.trans_eq (hdR_eq (by simp) (by simp)) h4)))
    exact h5.ofEq (hdR_eq rfl (by simp [ustoreN])) (hdR_eq rfl (by simp [ustoreN_one, uOf]))
  | succ j =>
    obtain ⟨c, u2, hu, hc, hu2⟩ := uOf_cons x
    obtain ⟨Ul, hUl'⟩ : ∃ Ul, Ul = ucs (uOf x) (List.replicate j 0) := ⟨_, rfl⟩
    have hUl : NoB Ul := by rw [hUl']; exact ucs_noB x _
    have hu0 : uc (uOf x) 0 0 = [1, 0, c] ++ u2 := by simp [uc, hu]
    have hu1 : uc (uOf x) 0 1 = [1, 1, c] ++ u2 := by simp [uc, hu]
    have hu0' : uc (uOf x) 0 0 = [1, 0] ++ bitsOf x ++ [2] := by simp [uc, uOf]
    have e0 : ustoreN x (j + 1) = Ul ++ [1, 0, c] ++ u2 := by
      rw [ustoreN_succ, hu0, ← hUl']
      simp
    have e1 : ustoreN x (j + 1 + 1) = Ul ++ [1, 1, c] ++ u2 ++ [1, 0] ++ bitsOf x ++ [2] := by
      rw [ustoreN_succ, List.replicate_succ, ucs_cons, ← hUl', hu0', hu1]
      simp
    have hSx : NoB (Ul ++ [1, 1, c] ++ u2) := by
      have h1' : (1 : Nat) ∈ NB := by simp [NB]
      have hc' : c ∈ NB := by rcases mem_bits hc with rfl | rfl <;> simp [NB]
      have := (hUl.app (NoB.cons h1' (NoB.cons h1' (NoB.cons hc' hu2.noB))))
      simpa using this
    have h1 := uA1n L Rt Ul u2 c hc hL hRt hUl hu2
    have h2 := uA2 Jl Jr (bitsOf x) Mid (Ul ++ [1, 1, c] ++ u2) hJl hJr hs hMid hSx
    have h3 := uLoop Jl Jr Mid (Ul ++ [1, 1, c] ++ u2) hJl hJr hMid hSx (bitsOf x) [] [] hs Bits.nil Bits.nil
    have h4 := uEnd Jl Jr (bitsOf x) Mid (Ul ++ [1, 1, c] ++ u2) (bitsOf x) hJl hJr hs hMid hSx hs
    have h5 := (h1.trans_eq (hd_eq (by rw [hLR] <;> simp) rfl) (h2.trans_eq (hdR_eq (by simp) (by simp))
      (h3.trans_eq (hdR_eq (by simp) (by simp)) h4)))
    exact h5.ofEq (hdR_eq rfl (by rw [e0]; simp)) (hdR_eq rfl (by rw [e1]; simp))


theorem sym4_ustoreN (x : List Bool) (k : Nat) : Sym4 (ustoreN x k) := by
  cases k with
  | zero => exact Sym4.nil
  | succ j => rw [ustoreN_eq]; exact sym4_storeOf x _ _

/-- The walk back through the decider code, one unit per step: from `UDW` with the walker after `Jlr.reverse`
to the walker at home (`WB2` on the blank left of it). -/
theorem walkUnits (x : List Bool) (Mid : List Nat) (hMid : NoB Mid) :
    ∀ (Jlr Jr : List Nat) (k : Nat), Bits Jlr → Bits Jr →
      mhBase.Reach
        (hdR QMH.UDW [0] (Jlr.reverse ++ 1 :: (Jr ++ 1 :: (bitsOf x ++ 1 :: (Mid ++ 0 :: ustoreN x k)))))
        (hd Q.WB2 [0] (1 :: (Jlr.reverse ++ Jr ++ 1 :: (bitsOf x ++ 1 :: (Mid ++
          0 :: ustoreN x (k + Jlr.length))))))
  | [], Jr, k, _, hJr => by
    have hs : Bits (bitsOf x) := Bits.ofB x
    have hR : Sym4 (bitsOf x ++ 1 :: (Mid ++ 0 :: ustoreN x k)) :=
      hs.sym4.app (Sym4.cons (by simp [ALL]) (hMid.sym4.app (Sym4.cons (by simp [ALL]) (sym4_ustoreN x k))))
    exact (udwHome Jr _ hJr hR).ofEq (by simp) (by simp)
  | j :: Jlr, Jr, k, hJlr, hJr => by
    have hs : Bits (bitsOf x) := Bits.ofB x
    have hj : j ∈ bits := hJlr.head
    have hJl : Bits Jlr.reverse := fun a ha => hJlr.tail a (List.mem_reverse.mp ha)
    have hR : Sym4 (bitsOf x ++ 1 :: (Mid ++ 0 :: ustoreN x k)) :=
      hs.sym4.app (Sym4.cons (by simp [ALL]) (hMid.sym4.app (Sym4.cons (by simp [ALL]) (sym4_ustoreN x k))))
    have h1 := udwStep Jlr.reverse Jr _ j hj hJl hJr hR
    have hRt : NoB (Jr ++ 1 :: (bitsOf x ++ 1 :: Mid)) :=
      hJr.noB.app (NoB.cons (by simp [NB]) (hs.noB.app (NoB.cons (by simp [NB]) hMid)))
    have hL : Sym4 (Jlr.reverse ++ [1, j]) := by
      have h1' : (1 : Nat) ∈ ALL := by simp [ALL]
      have hj' : j ∈ ALL := by rcases mem_bits hj with rfl | rfl <;> simp [ALL]
      exact hJl.sym4.app (Sym4.cons h1' (Sym4.cons hj' Sym4.nil))
    have h2 := unitApp x Jlr.reverse (j :: Jr) Mid (Jlr.reverse ++ [1, j]) (Jr ++ 1 :: (bitsOf x ++ 1 :: Mid))
      hJl (Bits.cons hj hJr) hMid hL hRt (by simp) k
    have h3 := walkUnits x Mid hMid Jlr (j :: Jr) (k + 1) hJlr.tail (Bits.cons hj hJr)
    have e1 : hdR QMH.U0 ([0] ++ Jlr.reverse ++ [1, j]) (Jr ++ [1] ++ (bitsOf x ++ 1 :: (Mid ++ 0 :: ustoreN x k))) =
        hdR QMH.U0 (Jlr.reverse ++ [1, j]) (Jr ++ 1 :: (bitsOf x ++ 1 :: Mid) ++ 0 :: ustoreN x k) := by
      rw [show ([0] ++ Jlr.reverse ++ [1, j]) = 0 :: (Jlr.reverse ++ [1, j]) by simp, hdR_lead0]
      exact hdR_eq rfl (by simp)
    have h4 := h1.trans_eq e1 (h2.trans h3)
    have e3 : k + 1 + Jlr.length = k + (j :: Jlr).length := by simp; omega
    exact h4.ofEq (hdR_eq (by simp) (by simp)) (hd_eq rfl (by rw [e3]; simp))

end ZP.MH
