"""One-off: build ZP/PairLNLV.lean (the verifier half of the `Z_LNL` pair) from the machine-independent parts of
ZP/Pair.lean plus the new setup / run lemmas for the one-way verifier."""
import re

pair = open('ZP/Pair.lean').read()


def block(name):
    m = re.search(r'((?:/--[^\n]*-/\n)?theorem %s .*?)\n\n' % name, pair, re.S)
    return m.group(1)


def fix(t):
    return t.replace('zpLogic', 'zlnlLogic').replace('zpBase', 'zlnlLogic')


head = '''module

public import ZP.PairLNLSeg

@[expose] public section

/-!
# `Z_LNL` pair: the verifier half

The loops of the outer machine (`BLK`, the guest and code copies), the run setup with the dummy cell, one whole
verifier run (`runFromL`), and the certificate loop `vLoopL` / `vFullL` with `run1` and `inLNL`.
-/

namespace ZP.MH

open ZP

/-! ## Small facts -/

'''

facts = ['Bits.rev', 'bits_all', 'o13_noB', 't3_noB', 'z2_noB', 'rep_t3', 'rep_z2', 'one_nb', 'rep_snoc_eq',
         'bitsOf_nil', 'bitsOf_reverse', 'bitsOf_len', 'blkW_full']

mid1 = '''
/-- `blkW` blocks of full width: `i` of them. -/
def FWn (n i : Nat) : List Nat := FWr (List.replicate i (n, n + 1))

theorem FWn_succ (n i : Nat) : FWn n (i + 1) = FWn n i ++ (1 :: List.replicate (n + 1) 3) := by
  show FWr (List.replicate i (n, n + 1)) ++ blkW n (n + 1) = _
  rw [blkW_full]
  rfl

theorem FWn_o13 (n : Nat) : ∀ i, ∀ a ∈ FWn n i, a ∈ O13
  | 0 => fun _ h => by cases h
  | i + 1 => by
    intro a ha
    rw [FWn_succ] at ha
    rcases List.mem_append.mp ha with h | h
    · exact FWn_o13 n i a h
    · rcases List.mem_cons.mp h with rfl | h
      · simp [O13]
      · rw [List.eq_of_mem_replicate h]; simp [O13]

/-! ## Loops of the outer machine -/

'''

loops = ['copyLoop', 'blkCopy', 'gcLoop', 'qcLoop']

mid2 = r'''
/-! ## Pair start: `lay` to the first `GC` -/

theorem phase1L (j s : List Nat) (hj : ∀ a ∈ j, a ∈ bits) (hs : ∀ a ∈ s, a ∈ bits) :
    zlnlLogic.Reach1 (L0.den [j, s]) (P1.den [j, s]) := by
  have hA : zlnlLogic.Reach1 (L0.den [j, s]) (F1.den [j, [], s]) :=
    check1 (sets := [bits, bits]) (E := []) (ρ := [[0], [], [1]]) (k := 9)
      (Valid.cons hj (Valid.cons hs (Valid.nil _))) trivial (by decide +kernel)
  have hL : zlnlLogic.Reach (F1.den [j, [], s]) (F1.den [j, [] ++ s, []]) := by
    refine LTM.Reach.fold (S := bits) (fun u v => F1.den [j, u, v]) ?_ s [] (nil_valid _) hs
    intro u b v hb hu hv
    have hval : Valid [bits, bits, bits] [j, u, v] :=
      Valid.cons hj (Valid.cons hu (Valid.cons hv (Valid.nil _)))
    rcases mem_bits hb with rfl | rfl
    · exact body (E := []) (i := 2) (i' := 1) (k := 9) hval trivial
        (by show 2 < 3; decide) (by show 1 < 3; decide) (by decide +kernel)
    · exact body (E := []) (i := 2) (i' := 1) (k := 9) hval trivial
        (by show 2 < 3; decide) (by show 1 < 3; decide) (by decide +kernel)
  have hB : zlnlLogic.Reach (F1.den [j, s, []]) (P1.den [j, s]) :=
    check (sets := [bits, bits, bits]) (E := [2]) (ρ := [[0], [1]]) (k := 19)
      (Valid.cons hj (Valid.cons hs (Valid.cons (nil_valid _) (Valid.nil _)))) ⟨rfl, trivial⟩
      (by decide +kernel)
  exact (hA.trans hL).trans hB

/-! ## Run setup: copy the source left, the code into `Q`, rotate once -/

theorem setupL (W1 Vq : List Nat) (Pb Xb : List Bool) (Rest W F : List Nat)
    (hV : 1 :: W1 = Vq ++ [1]) (hVq : NoB Vq) (hR : Sym4 Rest) (hW : NoB W) (hF : NoB F)
    (hWF : W1 ++ (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: Rest)) = W ++ 1 :: F) :
    ∃ g, 1 ≤ g ∧ zlnlLogic.Reach (hdR Q.GC (1 :: 2 :: (1 :: W1 ++ (bitsOf Pb ++ [1]))) (bitsOf Xb ++ 1 :: Rest))
      (Bv (rot (Pb.reverse ++ [false])) g ⟨[], Xb.head?, Xb.tail⟩ W F) := by
  have hVq' : NoB (2 :: Vq) := NoB.cons (by simp [NB]) hVq
  have hVn : NoB ((2 :: Vq) ++ [1]) := hVq'.app (NoB.cons one_nb NoB.nil)
  have hP : Bits (bitsOf Pb) := Bits.ofB Pb
  have hX : Bits (bitsOf Xb) := Bits.ofB Xb
  have hXr : Bits (bitsOf Xb).reverse := bitsOf_rev Xb
  have h1 := gcLoop ((2 :: Vq) ++ [1]) (bitsOf Pb) Rest hVn hP hR (bitsOf Xb) [] Bits.nil hX
  have h2 := gcEnd (bitsOf Xb).reverse ((2 :: Vq) ++ [1]) (bitsOf Pb) (bitsOf Xb) Rest hXr hVn hP hX hR
  have h3 := qcLoop (bitsOf Xb).reverse ((2 :: Vq) ++ [1]) (bitsOf Xb) Rest hXr hVn hX hR
    (bitsOf Pb).reverse [] hP.rev Bits.nil
  have h4 := qcEnd (bitsOf Pb) (bitsOf Xb).reverse (2 :: Vq) (bitsOf Xb) Rest hP hXr hVq' hX hR
  have e0 : hdR Q.GC (1 :: 2 :: (1 :: W1 ++ (bitsOf Pb ++ [1]))) (bitsOf Xb ++ 1 :: Rest) =
      hdR Q.GC (([] : List Nat).reverse ++ 1 :: (((2 :: Vq) ++ [1]) ++ (bitsOf Pb ++ 1 :: [])))
        (bitsOf Xb ++ 1 :: Rest) := by
    rw [hV]; simp
  have hA := (h1.of_eq e0.symm (by simp)).trans (h2.trans ((h3.of_eq (by simp) (by simp)).trans h4))
  have hG : Sym4 (0 :: ((bitsOf Xb).reverse ++ 1 :: ((2 :: Vq) ++ 1 :: (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: Rest))))) :=
    Sym4.cons (by simp [ALL]) (hXr.sym4.app (Sym4.cons (by simp [ALL]) (hVq'.sym4.app (Sym4.cons (by simp [ALL])
      (hP.sym4.app (Sym4.cons (by simp [ALL]) (hX.sym4.app (Sym4.cons (by simp [ALL]) hR))))))))
  obtain ⟨R', H, hrot, hH, -, hr⟩ := rotate rotNormal (Pb.reverse ++ [false]) (by simp) _ hG
  rw [rst_hd, rnav_hd] at hr
  have hcode : (bitsOf (Pb.reverse ++ [false])).reverse = 2 :: bitsOf Pb := by
    simp [bitsOf]
  have hB0 := hA.trans (lift (hr.ofEq (by rw [hcode]) rfl))
  have eT : Vq ++ 1 :: (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: Rest)) = 1 :: (W ++ 1 :: F) := by
    have e : Vq ++ 1 :: (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: Rest)) =
        (Vq ++ [1]) ++ (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: Rest)) := by simp
    rw [e, ← hV, List.cons_append, hWF]
  have hX1 : Sym4 (1 :: (W ++ 1 :: F)) := (NoB.cons one_nb (hW.app (NoB.cons one_nb hF))).sym4
  have hRr := bits_of_eq hrot
  have hrr : (bitsOf (rot (Pb.reverse ++ [false]))).reverse = 2 :: R'.reverse := by rw [hrot]; simp
  obtain ⟨k, hk⟩ : ∃ k, H.length = k + 1 := ⟨entryOnes (Pb.reverse ++ [false]) + 1, by omega⟩
  cases Xb with
  | nil =>
    have hB := segB R'.reverse [] (1 :: (W ++ 1 :: F)) k 0 0 0 2 (Or.inl rfl) (by simp [bits]) hRr Bits.nil hX1
    refine ⟨k + 1, by omega, hB0.trans (lift (hB.ofEq ?_ ?_))⟩
    · rw [hk]
      simp only [List.cons_append]
      rw [eT]
      simp [List.replicate_succ, rep_cons_comm, bitsOf]
    · unfold Bv Zp.Lw Zp.Rw
      rw [hrr]
      simp [cellN, bitsOf, List.replicate_succ, rep_cons_comm]
  | cons x xt =>
    have hB := segB R'.reverse (bitsOf xt.reverse) (1 :: (W ++ 1 :: F)) (k + 1) 0 0 (bn x) 2 (bn_cases x)
      (by simp [bits]) hRr (Bits.ofB _) hX1
    refine ⟨k + 1 + 1, by omega, hB0.trans (lift (hB.ofEq ?_ ?_))⟩
    · rw [hk]
      simp only [List.cons_append]
      rw [eT]
      simp [List.replicate_succ, rep_cons_comm, bitsOf_reverse, bitsOf_cons]
    · unfold Bv Zp.Lw Zp.Rw
      rw [hrr]
      simp [cellN_some, bitsOf, List.replicate_succ, rep_cons_comm]

theorem inv0 (Pb : List Bool) : InvR (rot (Pb.reverse ++ [false])) := by
  apply inv_rot
  refine ⟨by simp, fun hl => ?_, fun hl => ?_⟩
  · rcases Pb with _ | ⟨a, Pb⟩
    · rfl
    · simp at hl
  · rcases Pb with _ | ⟨a, _ | ⟨b, Pb⟩⟩
    · simp at hl
    · simp
    · simp at hl

/-- One guest run from the setup position, to the dispatch state. -/
theorem runFromL (W1 Vq : List Nat) (Pb Xb : List Bool) (Rest W : List Nat) (ds : List Dg)
    (hV : 1 :: W1 = Vq ++ [1]) (hVq : NoB Vq) (hR : Sym4 Rest) (hW : NoB W)
    (hds : Dig ds) (hne : ds ≠ [])
    (hWF : W1 ++ (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: Rest)) = W ++ 1 :: FWr ds) :
    ∃ ds', Dig ds' ∧ ds'.map Prod.fst = ds.map Prod.fst ∧
      zlnlLogic.Reach (hdR Q.GC (1 :: 2 :: (1 :: W1 ++ (bitsOf Pb ++ [1]))) (bitsOf Xb ++ 1 :: Rest))
        (RV (run1 Pb Xb (valr ds)) W (FWr ds')) := by
  obtain ⟨g, hg, h1⟩ := setupL W1 Vq Pb Xb Rest W (FWr ds) hV hVq hR hW (FWr_noB ds) hWF
  have hz : (⟨[], Xb.head?, Xb.tail⟩ : Zp).WF := by
    unfold Zp.WF
    cases Xb with
    | nil => intro _; rfl
    | cons x xt => intro h; simp at h
  obtain ⟨ds', hd', hl', h2⟩ := run1I W hW (valr ds) _ g _ ds (inv0 Pb) hg hz hds hne rfl
  have ht : (⟨[], Xb.head?, Xb.tail⟩ : Zp).tape = fun i => Xb[i]? := by
    cases Xb <;> rfl
  rw [ht] at h2
  exact ⟨ds', hd', hl', h1.trans (h2.ofEq rfl rfl)⟩

'''

counters = pair[pair.index('/-! ## Binary counters'):pair.index('/-! ## The verifier -/')]

verif = r'''
/-! ## The verifier -/

def tflag : Bool → List Nat
  | true => [3]
  | false => []

/-- Verifier run setup, certificate counter `cl` (least significant first). -/
def GCv (j : List Nat) (Sb cl : List Bool) : ZC :=
  hdR Q.GC (1 :: 2 :: (1 :: (j ++ [1]) ++ (bitsOf Sb ++ [1])))
    (bitsOf cl.reverse ++ 1 :: blkW Sb.length (Sb.length + 1))

/-- Truth flag written, `GRB` after it. -/
def TR (j : List Nat) (Sb : List Bool) (b : Bool) : ZC :=
  hdR Q.GRB (1 :: (j ++ 1 :: (bitsOf Sb ++ 1 :: 1 :: (tflag b ++ [1])))) []

theorem split2 (u : List Bool) (F : List Nat) (hu : u ≠ []) (hF : NoB F) :
    ∃ c y Y, bitsOf u ++ 1 :: F = c :: y :: Y ∧ c ∈ bits ∧ y ∈ NB ∧ NoB Y := by
  match u, hu with
  | [x], _ => exact ⟨bn x, 1, F, rfl, bn_bits x, one_nb, hF⟩
  | x :: x' :: u', _ =>
    exact ⟨bn x, bn x', bitsOf u' ++ 1 :: F, rfl, bn_bits x, by cases x' <;> simp [bn, NB],
      (Bits.ofB u').noB.app (NoB.cons one_nb hF)⟩

/-- One verifier pass: accept, underflow, or decrement and refill. -/
theorem vStepL (j : List Nat) (hj : Bits j) (Sb cl : List Bool) (hcl : cl.length = Sb.length + 1) :
    (run1 Sb cl.reverse (Sb.length + 1) = true →
      zlnlLogic.Reach (GCv j Sb cl) (TR j Sb true)) ∧
    (run1 Sb cl.reverse (Sb.length + 1) = false → cl = List.replicate (Sb.length + 1) false →
      zlnlLogic.Reach (GCv j Sb cl) (TR j Sb false)) ∧
    (run1 Sb cl.reverse (Sb.length + 1) = false → ∀ k r, cl = List.replicate k false ++ true :: r →
      zlnlLogic.Reach (GCv j Sb cl) (GCv j Sb (List.replicate k true ++ false :: r))) := by
  have hW : NoB (j ++ 1 :: (bitsOf Sb ++ 1 :: bitsOf cl.reverse)) :=
    hj.noB.app (NoB.cons one_nb ((Bits.ofB _).noB.app (NoB.cons one_nb (Bits.ofB _).noB)))
  obtain ⟨ds', hd', hl', h⟩ := runFromL (j ++ [1]) (1 :: j) Sb cl.reverse
    (blkW Sb.length (Sb.length + 1)) (j ++ 1 :: (bitsOf Sb ++ 1 :: bitsOf cl.reverse))
    [(Sb.length, Sb.length + 1)]
    rfl (NoB.cons one_nb hj.noB) (blkW_noB _ _).sym4 hW
    (fun d hd => by simp at hd; subst hd; exact Nat.le_refl _) (by simp) (by simp [FWr])
  have hv : valr [(Sb.length, Sb.length + 1)] = Sb.length + 1 := by simp [valr]
  rw [hv] at h
  obtain ⟨d, rfl⟩ : ∃ d, ds' = [(Sb.length, d)] := by
    rcases ds' with _ | ⟨⟨n, d⟩, _ | ⟨e, t⟩⟩
    · simp at hl'
    · simp at hl'
      exact ⟨d, by rw [hl']⟩
    · simp at hl'
  have hdd : d ≤ Sb.length + 1 := hd' (Sb.length, d) (by simp)
  have hF : FWr [(Sb.length, d)] = 1 :: (List.replicate d 3 ++ List.replicate (Sb.length + 1 - d) 2) := by
    simp [FWr, blkW]
  have hRE : ∀ o, RV o (j ++ 1 :: (bitsOf Sb ++ 1 :: bitsOf cl.reverse)) (FWr [(Sb.length, d)]) =
      hdR (dpOf (bn o)) [1] (j ++ 1 :: (bitsOf Sb ++ 1 :: (bitsOf cl.reverse ++ 1 :: FWr [(Sb.length, d)]))) := by
    intro o; unfold RV; simp
  have hne : cl.reverse ≠ [] := by
    intro e
    have := congrArg List.length e
    simp [hcl] at this
  refine ⟨fun ho => ?_, fun ho hc => ?_, fun ho k r hc => ?_⟩
  · rw [ho, hRE] at h
    obtain ⟨c, y, Y, eS, hc, hy, hY⟩ := split2 cl.reverse (FWr [(Sb.length, d)]) hne (FWr_noB _)
    have hA := vAcc j (bitsOf Sb) Y c y hj (Bits.ofB _) hY hc hy
    exact (h.ofEq rfl rfl).trans (hA.of_eq (by rw [← eS]; simp [dpOf, bn]) (by simp [TR, tflag]))
  · rw [ho, hRE] at h
    have hcr : bitsOf cl.reverse = 2 :: List.replicate Sb.length 2 := by
      rw [hc]; simp [bitsOf, List.replicate_succ, rep_snoc_eq]
    have hU := vUnder j (bitsOf Sb) (List.replicate Sb.length 2) (FWr [(Sb.length, d)]) hj (Bits.ofB _)
      (rep_z2 _) (FWr_noB _)
    exact (h.ofEq rfl rfl).trans (hU.of_eq (by rw [hcr]; simp [dpOf, bn]) (by simp [TR, tflag]))
  · rw [ho, hRE] at h
    have hcr : cl.reverse = r.reverse ++ true :: List.replicate k false := by rw [hc]; simp
    have hcr' : (List.replicate k true ++ false :: r).reverse = r.reverse ++ false :: List.replicate k true := by
      simp
    have hDE : List.replicate d 3 ++ List.replicate (Sb.length + 1 - d) 3 = List.replicate (Sb.length + 1) 3 := by
      rw [List.replicate_append_replicate]
      congr 1
      omega
    cases hr : r.reverse with
    | nil =>
      have hE := vRejE j (bitsOf Sb) (List.replicate k 2) (List.replicate d 3)
        (List.replicate (Sb.length + 1 - d) 2) hj (Bits.ofB _) (rep_z2 _) (rep_t3 _) (rep_z2 _)
      refine (h.ofEq rfl rfl).trans (hE.of_eq ?_ ?_)
      · rw [hF, hcr, hr]
        simp [dpOf, bn, bitsOf]
      · unfold GCv
        rw [hcr', hr]
        simp only [List.length_replicate]
        rw [hDE]
        simp [bitsOf, blkW]
    | cons x rr =>
      have hC := vRejC j (bitsOf Sb) (bitsOf rr) (List.replicate k 2) (List.replicate d 3)
        (List.replicate (Sb.length + 1 - d) 2) (bn x) hj (Bits.ofB _) (Bits.ofB _) (rep_z2 _) (rep_t3 _)
        (rep_z2 _) (bn_bits x)
      refine (h.ofEq rfl rfl).trans (hC.of_eq ?_ ?_)
      · rw [hF, hcr, hr]
        simp [dpOf, bn, bitsOf]
      · unfold GCv
        rw [hcr', hr]
        simp only [List.length_replicate]
        rw [hDE]
        simp [bitsOf, blkW, bn]

'''

loopv = pair[pair.index('/-- The verifier loop from counter'):pair.index('/-! ## From `lay` to the verifier -/')]
loopv = (loopv.replace('theorem vLoop ', 'theorem vLoopL ').replace('theorem vFull ', 'theorem vFullL ')
         .replace('vStep j', 'vStepL j').replace('vLoop j', 'vLoopL j').replace('inL Sb', 'inLNL Sb')
         .replace('unfold inL', 'unfold inLNL').replace('run Sb', 'run1 Sb'))

lay = r'''
/-! ## From `lay` to the verifier -/

theorem lay_hdR (J S : Nat) : lay J S = hdR Q.GRB (1 :: (bitsOf (str J) ++ 1 :: bitsOf (str S))) [] := by
  rw [lay_den]
  exact den_tapeR (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (by osimp) (by osimp)

theorem P1_hdR (j s : List Nat) :
    P1.den [j, s] = hdR Q.GRB (1 :: (j ++ 1 :: (s ++ 1 :: (List.replicate s.length 3 ++ [3, 1])))) [] :=
  den_tapeR (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 1 (.const 3), .sym 3, .sym 1])
    (by osimp) (by osimp)

theorem vStartL (J S : Nat) :
    zlnlLogic.Reach1 (lay J S) (GCv (bitsOf (str J)) (str S) (List.replicate ((str S).length + 1) true)) := by
  have hj := Bits.ofB (str J)
  have hs := Bits.ofB (str S)
  have h1 := phase1L _ _ hj hs
  rw [← lay_den, P1_hdR] at h1
  have hT : ∀ a ∈ List.replicate (bitsOf (str S)).length 3 ++ [3, 1], a ∈ O13 := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · rw [List.eq_of_mem_replicate h]; simp [O13]
    · simp at h
      rcases h with rfl | rfl <;> simp [O13]
  have h2 := blkCopy [] (bitsOf (str J)) (bitsOf (str S)) _ Bits.nil hj hs hT
  have h3 := blkVerL (bitsOf (str J)) (bitsOf (str S)) (List.replicate (bitsOf (str S)).length 3) hj hs
    (rep_t3 _)
  refine h1.trans ((h2.of_eq (by simp) rfl).trans (h3.of_eq ?_ ?_))
  · simp [rep_cons_comm]
  · unfold GCv
    simp [bitsOf, blkW, List.replicate_succ, rep_cons_comm]

end ZP.MH
'''

out = [fix(head)]
for n in facts:
    out.append(fix(block(n)) + '\n')
out.append(mid1)
for n in loops:
    t = fix(block(n))
    t = t.replace('zlnlLogic.Reach', 'zlnlLogic.Reach')
    out.append(t + '\n')
out.append(mid2)
out.append(fix(counters))
out.append(verif)
out.append(fix(loopv))
out.append(lay)
open('ZP/PairLNLV.lean', 'w').write('\n'.join(out).replace('.of_eq', '.ofEq'))
