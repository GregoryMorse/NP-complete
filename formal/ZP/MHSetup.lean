module

public import ZP.MHRun
public import ZP.MHDec

@[expose] public section

/-!
# Multihead run: the setup (code copy, rotation, `segB`)

From the code-copy state `QC` to the interpreter state `Bd`, for every machine `L` with `mhBase.Ext L`.
The block `Vq` between the first `M` and the code is `[]` for the decider, `1 :: J` for the verifier.
-/

namespace ZP.MH

open ZP

theorem setupMH (L : LTM) (hext : mhBase.Ext L) (Vq : List Nat) (Pb : List Bool) (X : List Nat)
    (R0 W F E : List Nat) (hVq : NoB Vq) (hX : Bits X) (hR0 : NoB R0) (hE : Sym4 E)
    (hW : NoB W) (hF : NoB F) (hFb : ∃ a ∈ F, a ∈ bits)
    (hWF : Vq ++ 1 :: (bitsOf Pb ++ 1 :: (X ++ 1 :: R0)) = 1 :: (W ++ 1 :: F)) :
    ∃ g, 1 ≤ g ∧ L.Reach
      (hd Q.QC (1 :: 1 :: (Vq ++ 1 :: bitsOf Pb)) (1 :: (X ++ 1 :: (R0 ++ 0 :: E))))
      (Bd (rot (Pb.reverse ++ [false])) g none (1 :: (W ++ 1 :: F)) (0 :: E)) := by
  have hP : Bits (bitsOf Pb) := Bits.ofB Pb
  have hV1 : NoB (Vq ++ [1]) := hVq.app (NoB.cons one_nb NoB.nil)
  have hRest : Sym4 (R0 ++ 0 :: E) := hR0.sym4.app (Sym4.cons (by simp [ALL]) hE)
  have h3 := qcLoop [] (Vq ++ [1]) X (R0 ++ 0 :: E) Bits.nil hV1 hX hRest (bitsOf Pb).reverse [] hP.rev
    Bits.nil
  have h4 := qcEnd (bitsOf Pb) [] Vq X (R0 ++ 0 :: E) hP Bits.nil hVq hX hRest
  simp only [List.reverse_reverse, List.nil_append, List.append_nil, List.cons_append, List.singleton_append,
    List.append_assoc] at h3 h4
  have hG : Sym4 (0 :: (1 :: (Vq ++ 1 :: (bitsOf Pb ++ 1 :: (X ++ 1 :: (R0 ++ 0 :: E)))))) :=
    Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) (hVq.sym4.app (Sym4.cons (by simp [ALL])
      (hP.sym4.app (Sym4.cons (by simp [ALL]) (hX.sym4.app (Sym4.cons (by simp [ALL]) hRest)))))))
  obtain ⟨R', H, hrot, hH, -, hr⟩ := rotate rotNormal (Pb.reverse ++ [false]) (by simp) _ hG
  rw [rst_hd, rnav_hd] at hr
  have hcode : (bitsOf (Pb.reverse ++ [false])).reverse = 2 :: bitsOf Pb := by
    simp [bitsOf]
  have hB0 := (h3.trans h4).trans (hr.ofEq (by rw [hcode]) rfl)
  have hVt : NoB (1 :: (W ++ 1 :: F)) := NoB.cons one_nb (hW.app (NoB.cons one_nb hF))
  obtain ⟨p, b, X', eV, hb, hX'⟩ := mb _ hVt (by
    obtain ⟨a, ha, hab⟩ := hFb
    exact ⟨a, List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ ha)), hab⟩)
  have hRr := bits_of_eq hrot
  have hrr : (bitsOf (rot (Pb.reverse ++ [false]))).reverse = 2 :: R'.reverse := by rw [hrot]; simp
  obtain ⟨k, hk⟩ : ∃ k, H.length = k + 1 := ⟨entryOnes (Pb.reverse ++ [false]) + 1, by omega⟩
  have eV2 : List.replicate p 1 ++ b :: (X' ++ 0 :: E) = (1 :: (W ++ 1 :: F)) ++ 0 :: E := by
    rw [eV]; simp
  have eT : Vq ++ 1 :: (bitsOf Pb ++ 1 :: (X ++ 1 :: (R0 ++ 0 :: E))) =
      List.replicate p 1 ++ b :: (X' ++ 0 :: E) := by
    rw [eV2]
    have : Vq ++ 1 :: (bitsOf Pb ++ 1 :: (X ++ 1 :: (R0 ++ 0 :: E))) =
        (Vq ++ 1 :: (bitsOf Pb ++ 1 :: (X ++ 1 :: R0))) ++ 0 :: E := by simp
    rw [this, hWF]
  have hXs : Sym4 (X' ++ 0 :: E) := hX'.app (Sym4.cons (by simp [ALL]) hE)
  have hB := segB R'.reverse [] (X' ++ 0 :: E) k 0 p 0 b (Or.inl rfl) hb hRr Bits.nil hXs
  refine ⟨k + 1, by omega, hext.reach (hB0.trans (hB.ofEq ?_ ?_))⟩
  · rw [hk]
    simp only [List.cons_append, List.nil_append] at eT ⊢
    rw [eT]
    simp [List.replicate_succ, rep_cons_comm]
  · unfold Bd
    rw [hrr]
    simp only [cellN]
    rw [eV2]
    simp [List.replicate_succ, rep_cons_comm]

end ZP.MH
