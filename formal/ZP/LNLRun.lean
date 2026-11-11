module

public import ZP.LNLSeg
public import ZP.MHLRun
public import ZP.AllDefs

@[expose] public section

/-!
# `Z_LNL`: a whole verifier run (the one-way guest)

The verifier run of `zlnl` is zp2's run (`ZP/Run.lean`) with a one-way head: the guest tape is a zipper, the
cells left of the head (`Rt`) sit right of `H`, followed by the dummy cell `0` that `VGD`/`VGE` write between `H`
and `M_g`. The tape is

    Q  0^g  0  Lw  c  H  Rw'  M_g  W  M_3  F        (Rw' = bitsOf (Rt ++ [false]))

`run1I`: from the step boundary the interpreter reaches the result state `DP1o` with
`o = run1Aux T R tape h`, where `T` is the value of the fuel odometer. The pieces shared with the multihead
run (`rotate`, `tokens`, `post`, `fuel`, `segB`, `segC`) are those of `mhBase`, lifted to `zlnlLogic`.
-/

namespace ZP.MH

open ZP

theorem lift {c c' : ZC} (h : mhBase.Reach c c') : zlnlLogic.Reach c c' := mhBase_ext_zlnlLogic.reach h

/-! ## The guest tape as a zipper -/

structure Zp where
  Rt : List Bool
  c : Option Bool
  Lt : List Bool

namespace Zp

def WF (z : Zp) : Prop := z.c = none → z.Lt = []

def list (z : Zp) : List Bool := z.Rt.reverse ++ (z.c.toList ++ z.Lt)

def tape (z : Zp) : Nat → Option Bool := fun i => z.list[i]?

/-- The cells right of the head, as they sit on the machine tape (left of the scanned cell). -/
def Lw (z : Zp) : List Nat := bitsOf z.Lt.reverse

/-- The cells left of the head, then the dummy cell, as they sit right of `H`. -/
def Rw (z : Zp) : List Nat := bitsOf z.Rt ++ [2]

/-- Write `w`; move right when `d`, else stay. -/
def mv : Zp → Bool → Bool → Zp
  | ⟨Rt, _, Lt⟩, w, true => ⟨w :: Rt, Lt.head?, Lt.tail⟩
  | ⟨Rt, _, Lt⟩, w, false => ⟨Rt, some w, Lt⟩

theorem tape_head {z : Zp} (hz : z.WF) : z.tape z.Rt.length = z.c := by
  rcases z with ⟨Rt, c, Lt⟩
  show (Rt.reverse ++ (c.toList ++ Lt))[Rt.length]? = c
  rw [List.getElem?_append_right (by simp)]
  simp only [List.length_reverse, Nat.sub_self]
  cases c with
  | none =>
    have e : Lt = [] := hz rfl
    subst e
    rfl
  | some x => rfl

theorem set_eq (A : List Bool) (c : Option Bool) (B : List Bool) (hc : c = none → B = []) (w : Bool) :
    (fun i => if i = A.length then some w else (A ++ (c.toList ++ B))[i]?) =
      fun i => (A ++ w :: B)[i]? := by
  funext i
  rcases Nat.lt_trichotomy i A.length with h | h | h
  · rw [if_neg (Nat.ne_of_lt h), List.getElem?_append_left h, List.getElem?_append_left h]
  · subst h
    simp
  · rw [if_neg (Nat.ne_of_gt h)]
    obtain ⟨k, rfl⟩ : ∃ k, i = A.length + (k + 1) := ⟨i - A.length - 1, by omega⟩
    have hle : A.length ≤ A.length + (k + 1) := Nat.le_add_right _ _
    rw [List.getElem?_append_right hle, List.getElem?_append_right hle, Nat.add_sub_cancel_left]
    cases c with
    | none => simp [hc rfl]
    | some x => simp

theorem mv_list (z : Zp) (w d : Bool) : (z.mv w d).list = z.Rt.reverse ++ w :: z.Lt := by
  rcases z with ⟨Rt, c, Lt⟩
  cases d
  · rfl
  · show (w :: Rt).reverse ++ (Lt.head?.toList ++ Lt.tail) = _
    cases Lt <;> simp

theorem mv_tape {z : Zp} (hz : z.WF) (w d : Bool) :
    (z.mv w d).tape = fun i => if i = z.Rt.length then some w else z.tape i := by
  have e := set_eq z.Rt.reverse z.c z.Lt hz w
  rw [List.length_reverse] at e
  show (fun i => (z.mv w d).list[i]?) = fun i => if i = z.Rt.length then some w else z.list[i]?
  rw [mv_list]
  exact e.symm

theorem mv_len (z : Zp) (w d : Bool) :
    (z.mv w d).Rt.length = if d then z.Rt.length + 1 else z.Rt.length := by
  rcases z with ⟨Rt, c, Lt⟩
  cases d <;> simp [mv]

theorem mv_WF (z : Zp) (w d : Bool) : (z.mv w d).WF := by
  rcases z with ⟨Rt, c, Lt⟩
  cases d
  · intro h; cases h
  · intro h
    cases Lt with
    | nil => rfl
    | cons _ _ => cases h

end Zp

/-! ## Configurations -/

/-- The step boundary of a verifier run. -/
def Bv (R : List Bool) (g : Nat) (z : Zp) (W F : List Nat) : ZC :=
  hd Q.BK2 ((bitsOf R).reverse ++ List.replicate g 0 ++ 0 :: (z.Lw ++ [cellN z.c]))
    (1 :: (z.Rw ++ 1 :: (W ++ 1 :: F)))

/-- The result state. -/
def RV (o : Bool) (W F : List Nat) : ZC := hdR (dpOf (bn o)) [1] (W ++ 1 :: F)

/-! ## The count-down -/

theorem cdStepV (R : List Bool) (hR : InvR R) (g : Nat) (Lw V : List Nat) (c : Nat) (hc : c ∈ bits)
    (hL : Bits Lw) (hV : NoB V) (hVb : ∃ a ∈ V, a ∈ bits) :
    ∃ g', 1 ≤ g' ∧ zlnlLogic.Reach
      (hd Q.BK2 ((bitsOf R).reverse ++ List.replicate g 0 ++ 0 :: (Lw ++ [c])) (1 :: V))
      (hd Q.BK2 ((bitsOf (rot R)).reverse ++ List.replicate g' 0 ++ 0 :: (Lw ++ [cdn c])) (1 :: V)) := by
  have hA := segAV (bitsOf R).reverse Lw V g c hc (bitsOf_rev R) hL hV
  have hX : Sym4 (List.replicate g 0 ++ 0 :: (Lw ++ cdn c :: 1 :: V)) :=
    (zeros4 g).app (Sym4.cons (by simp [ALL]) (hL.sym4.app (Sym4.cons (cdn_all c)
      (Sym4.cons (by simp [ALL]) hV.sym4))))
  obtain ⟨R', H, hrot, -, -, hr⟩ := rotate rotNormal R hR.1 _ hX
  rw [rst_hd, rnav_hd] at hr
  obtain ⟨p, b, X, rfl, hb, hX'⟩ := mb V hV hVb
  have hB := segB R'.reverse Lw X H.length g p (cdn c) b (cdn_cases c) hb (bits_of_eq hrot) hL hX'
  refine ⟨H.length + g + 1, by omega, hA.trans ((lift hr).trans ((lift hB).ofEq
    (hdR_eq rfl (by simp only [List.append_assoc])) (hd_eq ?_ rfl)))⟩
  rw [hrot]
  simp [List.replicate_succ, rep_rep]

/-- The whole count-down: `iota` rotations, leaving a blank scanned cell. -/
theorem countdownV (R : List Bool) (hR : InvR R) (g : Nat) (hg : 1 ≤ g) (Lw V : List Nat) (x : Option Bool)
    (hL : Bits Lw) (hV : NoB V) (hVb : ∃ a ∈ V, a ∈ bits) :
    ∃ g', 1 ≤ g' ∧ zlnlLogic.Reach
      (hd Q.BK2 ((bitsOf R).reverse ++ List.replicate g 0 ++ 0 :: (Lw ++ [cellN x])) (1 :: V))
      (hd Q.BK2 ((bitsOf (rotN (iota x) R)).reverse ++ List.replicate g' 0 ++ 0 :: (Lw ++ [0])) (1 :: V)) := by
  rcases x with _ | _ | _
  · exact ⟨g, hg, LTM.Reach.refl _ _⟩
  · obtain ⟨g', hg', h⟩ := cdStepV R hR g Lw V 2 (by simp [bits]) hL hV hVb
    exact ⟨g', hg', h⟩
  · obtain ⟨g1, _, h1⟩ := cdStepV R hR g Lw V 3 (by simp [bits]) hL hV hVb
    obtain ⟨g2, hg2, h2⟩ := cdStepV (rot R) (inv_rot hR) g1 Lw V 2 (by simp [bits]) hL hV hVb
    exact ⟨g2, hg2, h1.trans h2⟩

/-! ## Fuel decrement after the count-down -/

theorem decV (ds : List Dg) (hds : Dig ds) (Qw Lw Rw W : List Nat) (g : Nat)
    (hQ : Bits Qw) (hL : Bits Lw) (hR : Bits Rw) (hW : NoB W) :
    (0 < valr ds → ∃ ds', Dig ds' ∧ ds'.map Prod.fst = ds.map Prod.fst ∧ valr ds' + 1 = valr ds ∧
      zlnlLogic.Reach (hd Q.BK2 (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0])) (1 :: (Rw ++ 1 :: (W ++ 1 :: FWr ds))))
        (hd Q.FBACK (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0])) (1 :: (Rw ++ 1 :: (W ++ 1 :: FWr ds'))))) ∧
    (valr ds = 0 →
      zlnlLogic.Reach (hd Q.BK2 (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0])) (1 :: (Rw ++ 1 :: (W ++ 1 :: FWr ds))))
        (hd Q.EXH (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0]))
          (1 :: (Rw ++ 1 :: (W ++ 1 :: FWr (full ds)))))) := by
  have hC := lift (segC Qw Lw Rw W (FWr ds) g hQ hL hR hW (FWr_noB ds))
  have h1 : (1 : Nat) ∈ NB := by simp [NB]
  have hL0 : Sym4 (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0])) :=
    (hQ.sym4.app (zeros4 g)).app (Sym4.cons (by simp [ALL]) (hL.sym4.app (Sym4.cons (by simp [ALL]) Sym4.nil)))
  have hW1 : NoB (1 :: (Rw ++ 1 :: W)) := NoB.cons h1 (hR.noB.app (NoB.cons h1 hW))
  have hLL : Sym4 (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0]) ++ 1 :: (Rw ++ 1 :: W)) := hL0.app hW1.sym4
  have hF := fuel ds hds _ [] hLL Sym4.nil (Or.inl rfl)
  refine ⟨fun hpos => ?_, fun h0 => ?_⟩
  · obtain ⟨ds', hd', hm, hv, hr⟩ := hF.1 hpos
    have hwk := walkL Q.FBACK (Or.inl rfl) (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0]))
      (1 :: (Rw ++ 1 :: W) ++ [1]) (FWr ds' ++ []) hL0 (hW1.app (NoB.cons h1 NoB.nil))
      ((FWr_noB ds').sym4.app Sym4.nil)
    refine ⟨ds', hd', hm, hv, hC.trans ((lift hr).trans ((lift hwk).ofEq (hd_eq ?_ rfl) (hd_eq rfl ?_)))⟩
    · simp only [List.append_assoc]
    · simp
  · have hr := hF.2 h0
    have hwk := walkL Q.EXH (Or.inr rfl) (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0]))
      (1 :: (Rw ++ 1 :: W)) (1 :: (FWr (full ds) ++ [])) hL0 hW1
      (Sym4.cons (by simp [ALL]) ((FWr_noB _).sym4.app Sym4.nil))
    exact hC.trans ((lift hr).trans ((lift hwk).ofEq rfl (hd_eq rfl (by simp))))

/-! ## The peek: halt or write, move and rotate -/

theorem peekV (R1 : List Bool) (hR1 : InvR R1) (g : Nat) (hg : 1 ≤ g) (z : Zp) (W F : List Nat)
    (hW : NoB W) (hF : NoB F) (hFb : ∃ a ∈ F, a ∈ bits) :
    (R1.getD 2 false = false → zlnlLogic.Reach
      (hd Q.FBACK ((bitsOf R1).reverse ++ List.replicate g 0 ++ 0 :: (z.Lw ++ [0]))
        (1 :: (z.Rw ++ 1 :: (W ++ 1 :: F))))
      (RV (R1.getD 0 false) W F)) ∧
    (R1.getD 2 false = true → ∃ g', 1 ≤ g' ∧ zlnlLogic.Reach
      (hd Q.FBACK ((bitsOf R1).reverse ++ List.replicate g 0 ++ 0 :: (z.Lw ++ [0]))
        (1 :: (z.Rw ++ 1 :: (W ++ 1 :: F))))
      (Bv (rotN (entryOnes R1 + 1) (rot R1)) g' (z.mv (R1.getD 0 false) (R1.getD 1 false)) W F)) := by
  have hLw : Bits z.Lw := Bits.ofB _
  have hRw : Bits z.Rw := (Bits.ofB _).app (Bits.cons (by simp [bits]) Bits.nil)
  have h1 : (1 : Nat) ∈ NB := by simp [NB]
  have hW' : NoB (W ++ 1 :: F) := hW.app (NoB.cons h1 hF)
  rcases R1 with _ | ⟨r0, _ | ⟨r1, _ | ⟨r2, rest⟩⟩⟩
  · exact absurd hR1.1 (by simp)
  · have e := hR1.2.1 rfl
    simp only [List.cons.injEq, and_true] at e
    subst e
    refine ⟨fun _ => ?_, fun h => by simp at h⟩
    exact (segShort1V z.Lw z.Rw (W ++ 1 :: F) g hLw hRw hW').ofEq rfl (by simp [RV, dpOf, bn])
  · have e := hR1.2.2 rfl
    simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] at e
    subst e
    refine ⟨fun _ => ?_, fun h => by simp at h⟩
    have h := segShort2V z.Lw z.Rw (W ++ 1 :: F) g (bn r0) (bn_bits r0) hLw hRw hW'
    exact h.ofEq (hd_eq (by cases r0 <;> rfl) rfl) (by cases r0 <;> rfl)
  · have hrest : Bits (bitsOf rest).reverse := bitsOf_rev rest
    have hf : false ∈ r0 :: r1 :: r2 :: rest := hR1.1
    refine ⟨fun h2 => ?_, fun h2 => ?_⟩
    · have h2' : r2 = false := h2
      subst h2'
      have h := segHaltV (bitsOf rest).reverse z.Lw z.Rw (W ++ 1 :: F) g (bn r0) (bn r1) (bn_bits r0)
        (bn_bits r1) hrest hLw hRw hW'
      exact h.ofEq (hd_eq (by rw [bits3]; rfl) rfl) (by cases r0 <;> rfl)
    · have h2' : r2 = true := h2
      subst h2'
      have hcode : (bitsOf (r0 :: r1 :: true :: rest)).reverse = (bitsOf rest).reverse ++ [3, bn r1, bn r0] := by
        rw [bits3]; rfl
      show ∃ g', 1 ≤ g' ∧ zlnlLogic.Reach _ (Bv _ g' (z.mv r0 r1) W F)
      rw [hcode]
      have hQc : Bits ((bitsOf rest).reverse ++ [3, bn r1, bn r0]) :=
        hrest.app (Bits.cons (by simp [bits]) (Bits.cons (bn_bits r1) (Bits.cons (bn_bits r0) Bits.nil)))
      rcases z with ⟨Rt, c, Lt⟩
      cases r1 with
      | false =>
        -- stay: write `r0` into `c`
        obtain ⟨c0, Rw0, eR, hc0, hR0⟩ : ∃ c0 Rw0, Zp.Rw ⟨Rt, c, Lt⟩ = c0 :: Rw0 ∧ c0 ∈ bits ∧ Bits Rw0 := by
          cases Rt with
          | nil => exact ⟨2, [], rfl, by simp [bits], Bits.nil⟩
          | cons r Rt => exact ⟨bn r, bitsOf Rt ++ [2], rfl, bn_bits r, (Bits.ofB _).app (Bits.cons (by simp [bits]) Bits.nil)⟩
        have hm := segMv0L ((bitsOf rest).reverse) (bitsOf Lt.reverse) Rw0 (W ++ 1 :: F) g (bn r0) c0
          (bn_bits r0) hc0 hrest hLw hR0 hW'
        obtain ⟨g', hg', hp⟩ := post (r0 :: false :: true :: rest) hf (bitsOf Lt.reverse) (bn r0) 0 c0
          (Rw0 ++ 1 :: (W ++ 1 :: F)) g hLw (bn_cases r0) hc0
          ((hR0.noB.app (NoB.cons h1 hW')).sym4)
        rw [hcode] at hp
        refine ⟨g', hg', ?_⟩
        have e1 : (hd Q.FBACK ((bitsOf rest).reverse ++ [3, bn false, bn r0] ++ List.replicate g 0 ++ 0 ::
            (Zp.Lw ⟨Rt, c, Lt⟩ ++ [0])) (1 :: (Zp.Rw ⟨Rt, c, Lt⟩ ++ 1 :: (W ++ 1 :: F)))) =
            hd Q.FBACK ((bitsOf rest).reverse ++ [3, 2, bn r0] ++ List.replicate g 0 ++ [0] ++ bitsOf Lt.reverse ++ [0])
              ([1, c0] ++ Rw0 ++ [1] ++ (W ++ 1 :: F)) := by
          rw [eR]; simp [Zp.Lw, bn]
        rw [e1]
        refine (hm.ofEq rfl (hd_eq rfl (by simp))).trans (lift (hp.ofEq rfl ?_))
        · show _ = Bv _ g' ⟨Rt, some r0, Lt⟩ W F
          unfold Bv
          rw [cellN_some, show Zp.Rw ⟨Rt, some r0, Lt⟩ = c0 :: Rw0 from eR]
          simp [Zp.Lw]
      | true =>
        obtain ⟨c0, Rw0, eR, hc0, hR0⟩ : ∃ c0 Rw0, Zp.Rw ⟨Rt, c, Lt⟩ = c0 :: Rw0 ∧ c0 ∈ bits ∧ Bits Rw0 := by
          cases Rt with
          | nil => exact ⟨2, [], rfl, by simp [bits], Bits.nil⟩
          | cons r Rt => exact ⟨bn r, bitsOf Rt ++ [2], rfl, bn_bits r, (Bits.ofB _).app (Bits.cons (by simp [bits]) Bits.nil)⟩
        have hm := segMv1L ((bitsOf rest).reverse) (bitsOf Lt.reverse) Rw0 (W ++ 1 :: F) g (bn r0) c0
          (bn_bits r0) hc0 hrest hLw hR0 hW'
        have hX2 : Sym4 (c0 :: (Rw0 ++ 1 :: (W ++ 1 :: F))) :=
          (NoB.cons (by rcases mem_bits hc0 with rfl | rfl <;> simp [NB]) (hR0.noB.app (NoB.cons h1 hW'))).sym4
        have e1 : (hd Q.FBACK ((bitsOf rest).reverse ++ [3, bn true, bn r0] ++ List.replicate g 0 ++ 0 ::
            (Zp.Lw ⟨Rt, c, Lt⟩ ++ [0])) (1 :: (Zp.Rw ⟨Rt, c, Lt⟩ ++ 1 :: (W ++ 1 :: F)))) =
            hd Q.FBACK ((bitsOf rest).reverse ++ [3, 3, bn r0] ++ List.replicate g 0 ++ [0] ++ bitsOf Lt.reverse ++ [0])
              ([1, c0] ++ Rw0 ++ [1] ++ (W ++ 1 :: F)) := by
          rw [eR]; simp [Zp.Lw, bn]
        rw [e1]
        cases Lt with
        | nil =>
          have eR' : Zp.Rw ⟨r0 :: Rt, none, []⟩ = bn r0 :: (c0 :: Rw0) := by rw [← eR]; rfl
          obtain ⟨g0, rfl⟩ : ∃ g0, g = g0 + 1 := ⟨g - 1, by omega⟩
          obtain ⟨g', hg', hp⟩ := post (r0 :: true :: true :: rest) hf [] 0 0 (bn r0)
            (c0 :: (Rw0 ++ 1 :: (W ++ 1 :: F))) g0 Bits.nil (Or.inl rfl) (bn_bits r0) hX2
          rw [hcode] at hp
          refine ⟨g', hg', (hm.ofEq rfl (hd_eq rfl ?_)).trans (lift (hp.ofEq rfl ?_))⟩
          · simp [List.replicate_succ, rep_cons_comm, bitsOf]
          · show _ = Bv _ g' ⟨r0 :: Rt, none, []⟩ W F
            unfold Bv
            rw [eR']
            simp [Zp.Lw, bitsOf, cellN]
        | cons x Lt =>
          have eR' : Zp.Rw ⟨r0 :: Rt, some x, Lt⟩ = bn r0 :: (c0 :: Rw0) := by rw [← eR]; rfl
          obtain ⟨g', hg', hp⟩ := post (r0 :: true :: true :: rest) hf (bitsOf Lt.reverse) (bn x) 0 (bn r0)
            (c0 :: (Rw0 ++ 1 :: (W ++ 1 :: F))) g (Bits.ofB _) (bn_cases x) (bn_bits r0) hX2
          rw [hcode] at hp
          refine ⟨g', hg', (hm.ofEq rfl (hd_eq rfl ?_)).trans (lift (hp.ofEq rfl ?_))⟩
          · simp [Zp.Lw, bitsOf, bn]
          · show _ = Bv _ g' ⟨r0 :: Rt, some x, Lt⟩ W F
            unfold Bv
            rw [eR', cellN_some]
            simp [Zp.Lw]


/-! ## The whole run -/

theorem run1I (W : List Nat) (hW : NoB W) :
    ∀ T R g z ds, InvR R → 1 ≤ g → z.WF → Dig ds → ds ≠ [] → valr ds = T →
      ∃ ds', Dig ds' ∧ ds'.map Prod.fst = ds.map Prod.fst ∧
        zlnlLogic.Reach (Bv R g z W (FWr ds)) (RV (run1Aux T R z.tape z.Rt.length) W (FWr ds'))
  | T, R, g, z, ds, hR, hg, hz, hds, hne, hv => by
    have h1 : (1 : Nat) ∈ NB := by simp [NB]
    have hRw : Bits z.Rw := (Bits.ofB _).app (Bits.cons (by simp [bits]) Bits.nil)
    have hV : NoB (z.Rw ++ 1 :: (W ++ 1 :: FWr ds)) :=
      hRw.noB.app (NoB.cons h1 (hW.app (NoB.cons h1 (FWr_noB ds))))
    have hVb : ∃ a ∈ z.Rw ++ 1 :: (W ++ 1 :: FWr ds), a ∈ bits := by
      obtain ⟨a, ha, hab⟩ := fw_bit ds hne
      exact ⟨a, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_cons_of_mem _ ha))), hab⟩
    obtain ⟨g1, hg1, hcd⟩ := countdownV R hR g hg z.Lw _ z.c (Bits.ofB _) hV hVb
    have hR1 : InvR (rotN (iota z.c) R) := inv_rotN hR _
    have hD := decV ds hds (bitsOf (rotN (iota z.c) R)).reverse z.Lw z.Rw W g1 (bitsOf_rev _)
      (Bits.ofB _) hRw hW
    cases T with
    | zero =>
      refine ⟨full ds, fun d hd => ?_, by simp [full], ?_⟩
      · obtain ⟨_, -, rfl⟩ := List.mem_map.mp hd
        exact Nat.le_refl _
      · have hE := hD.2 hv
        obtain ⟨r, rest, e⟩ : ∃ r rest, rotN (iota z.c) R = r :: rest := by
          cases h : rotN (iota z.c) R with
          | nil => rw [h] at hR1; exact absurd hR1.1 (by simp)
          | cons r rest => exact ⟨r, rest, rfl⟩
        rw [e, bits1] at hE hcd
        have hx := segExhV (bitsOf rest).reverse z.Lw z.Rw (W ++ 1 :: FWr (full ds)) g1 (bn r)
          (bn_bits r) (bitsOf_rev _) (Bits.ofB _) hRw
          (hW.app (NoB.cons h1 (FWr_noB _)))
        exact (hcd.trans (hE.trans hx)).ofEq rfl (by simp [RV, run1Aux, dpOf, bn])
    | succ T =>
      obtain ⟨ds1, hd1, hl1, hv1, hdec⟩ := hD.1 (by omega)
      have hne1 : ds1 ≠ [] := by
        intro h; rw [h] at hl1; exact hne (List.map_eq_nil_iff.mp hl1.symm)
      have hP := peekV (rotN (iota z.c) R) hR1 g1 hg1 z W (FWr ds1) hW (FWr_noB ds1) (fw_bit ds1 hne1)
      simp only [run1Aux]
      rw [Zp.tape_head hz]
      cases h2 : (rotN (iota z.c) R).getD 2 false with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨ds1, hd1, hl1, hcd.trans (hdec.trans (hP.1 h2))⟩
      | true =>
        simp only [↓reduceIte]
        obtain ⟨g', hg', hm⟩ := hP.2 h2
        obtain ⟨ds2, hd2, hl2, ih⟩ := run1I W hW T _ g' _ ds1
          (inv_rotN (inv_rot hR1) _) hg' (Zp.mv_WF _ _ _) hd1 hne1 (by omega)
        rw [Zp.mv_tape hz, Zp.mv_len] at ih
        exact ⟨ds2, hd2, hl2.trans hl1, hcd.trans (hdec.trans (hm.trans ih))⟩
  termination_by T => T

end ZP.MH
