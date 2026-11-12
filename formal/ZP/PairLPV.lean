module

public import ZP.PairLP
public import ZP.MHSetup
public import ZP.MHUnits

@[expose] public section

/-!
# Z_LP: the verifier half of the pair

The truth flag `inLP s`: the units, the setup, one multihead run of `s` on `s`, the erase of the storage.
-/

namespace ZP.MH

open ZP

/-- The storage (and the rest right of the flag) is erased and `M_3` written after the flag. -/
theorem eraseV (A1 : List Nat) (c : Nat) (hA : Sym4 A1) (hc : c ∈ O13) (Y : List Nat) (hY : Eras Y) :
    zlpLogic.Reach (hdR Q.VA3 (A1 ++ [c]) Y) (hdR Q.GRB (A1 ++ [c, 1]) []) := by
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have hc' : c ∈ ALL := by simp [O13] at hc; rcases hc with rfl | rfl <;> simp [ALL]
  have hAc : Sym4 (A1 ++ [c]) := hA.app (Sym4.cons hc' Sym4.nil)
  obtain ⟨m, h1⟩ := eraseLoop zlpLogic Q.VA3 QLP.EY Q.VA4
    (fun c hc A R hA hR => vaN A R c hA hR hc) (fun A R hA hR => vaB A R hA hR)
    (fun c hc A R hA hR => vxN A R c hA hR hc) (fun A hA => vxE A hA) (fun A hA => vaE A hA)
    Y.length Y rfl hY (A1 ++ [c]) hAc
  have h2 := skipBack zlpLogic Q.VA4 (fun A R hA hR => vbB A R hA hR) m (A1 ++ [c]) [0] hAc
    (Sym4.cons h0 Sym4.nil)
  have hR0 : Sym4 (List.replicate m 0 ++ [0]) := (Sym4.rep m 0 h0).app (Sym4.cons h0 Sym4.nil)
  have h3 := vbF A1 (List.replicate m 0 ++ [0]) c hA hR0 hc
  have h4 := fbW (A1 ++ [c]) hAc
  have e : List.replicate m 0 ++ [0] = List.replicate (m + 1) 0 := by
    rw [List.replicate_succ', ]
  refine ((h1.trans h2).trans (h3.trans ?_))
  rw [e, hdR_zeros]
  exact h4.ofEq rfl (by simp)

/-- After the verifier's run: the truth flag, the storage erased. -/
theorem vPost (o : Bool) (j s Z : List Nat) (hj : Bits j) (hs : Bits s) (hZ : ∀ a ∈ Z, a ∈ Z2) (hZne : Z ≠ [])
    (F' : List Nat) (hF' : NoB F') (x : List Bool) (pos : List Nat) (cur : Nat) :
    zlpLogic.Reach (hdR (dpOf (bn o)) [1] (j ++ 1 :: (s ++ 1 :: (2 :: Z ++ 1 :: (F' ++ 0 :: storeOf x pos cur)))))
      (hdR Q.GRB (1 :: (j ++ 1 :: (s ++ 1 :: 1 :: (tflag o ++ [1])))) []) := by
  have h1u : (1 : Nat) ∈ ALL := by simp [ALL]
  have hZb : NoB Z := z2_noB hZ
  have hA0 : Sym4 ([1] ++ j ++ [1] ++ s ++ [1]) := by
    have : Sym4 (1 :: (j ++ 1 :: (s ++ [1]))) :=
      Sym4.cons h1u (hj.sym4.app (Sym4.cons h1u (hs.sym4.app (Sym4.cons h1u Sym4.nil))))
    simpa using this
  have hY : NoB (Z ++ 1 :: F') := hZb.app (NoB.cons one_nb hF')
  have hE := Eras_gap_store hY x pos cur
  cases o with
  | true =>
    obtain ⟨Z', rfl⟩ : ∃ Z', Z = 2 :: Z' := by
      cases Z with
      | nil => exact absurd rfl hZne
      | cons a t => exact ⟨t, by have := hZ a (List.mem_cons_self ..); simp [Z2] at this; rw [this]⟩
    have hY' : NoB (Z' ++ 1 :: F') := fun a ha => hY a (List.mem_cons_of_mem _ ha)
    have hE' := Eras_gap_store hY' x pos cur
    have h1 := vTrue0 j s (Z' ++ 1 :: (F' ++ 0 :: storeOf x pos cur)) hj hs
      (Eras.sym4 (by simpa using hE'))
    have h2 := eraseV ([1] ++ j ++ [1] ++ s ++ [1, 1]) 3
      (by simpa using hA0.app (Sym4.cons h1u Sym4.nil)) (by simp [O13])
      (Z' ++ 1 :: (F' ++ 0 :: storeOf x pos cur)) (by simpa using hE')
    refine (h1.ofEq (hdR_eq (by simp [dpOf, bn]) (by simp)) rfl).trans (h2.ofEq (hdR_eq (by simp) rfl) ?_)
    simp [tflag]
  | false =>
    have h1 := vFalse j s (Z ++ 1 :: (F' ++ 0 :: storeOf x pos cur)) hj hs
      (Eras.sym4 (by simpa using hE))
    have h2 := eraseV ([1] ++ j ++ [1] ++ s ++ [1]) 1 (by simpa using hA0) (by simp [O13])
      (Z ++ 1 :: (F' ++ 0 :: storeOf x pos cur)) (by simpa using hE)
    refine (h1.ofEq (hdR_eq (by simp [dpOf, bn]) (by simp)) rfl).trans (h2.ofEq (hdR_eq (by simp) rfl) ?_)
    simp [tflag]

end ZP.MH
