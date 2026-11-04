module

public import ZP.Defs
public import ZP.Logic
public import ZP.SymExec
public import ZP.Outer
public import ZP.Rot
public import ZP.Fuel
public import ZP.Interp

@[expose] public section

/-!
# Layer N3: a whole guest run

The guest tape is a zipper: cells left of the head (nearest first), the scanned cell,
cells right of the head (nearest first). `runI` shows that from the step boundary the
interpreter reaches the result state `DP1o` with `o = runAux T R tape h`, where `T` is
the value of the fuel odometer.
-/

namespace ZP

/-! ## Conversions and small facts -/

theorem rst_hd (q h : Nat) (R X : List Nat) : rst q h R [] X = hd q R.reverse X := by
  show (⟨q, [Item.blk 0 .id].reverse, [.blk 1 (.const h), .blk 2 .id], true⟩ : SC).den
    [R.reverse, [], X] = _
  exact den_tape (by simp [dR, Item.den, List.getD, map_id_app])
    (by simp [dR, Item.den, List.getD, map_id_app])

theorem map_const_len (c : Nat) : ∀ H : List Nat, H.map (Fn.const c).app = List.replicate H.length c
  | [] => rfl
  | _ :: H => by
    show c :: H.map (Fn.const c).app = c :: List.replicate H.length c
    rw [map_const_len c H]

theorem rnav_hd (h : Nat) (R H X : List Nat) :
    rnav h R H X = hdR Q.NAV [2] (R.reverse ++ 0 :: (List.replicate H.length h ++ X)) := by
  show (⟨Q.NAV, [Item.sym 2].reverse, [.blk 0 .id, .sym 0, .blk 1 (.const h), .blk 2 .id], false⟩ : SC).den
    [R.reverse, H, X] = _
  exact den_tapeR (by simp [dR, Item.den]) (by simp [dR, Item.den, List.getD, map_id_app, map_const_len])

theorem LTM.Reach.of_eq {M : LTM} {c1 c2 c3 c4 : ZC} (h : M.Reach c1 c2) (e1 : c1 = c3) (e2 : c2 = c4) :
    M.Reach c3 c4 := e1 ▸ e2 ▸ h

theorem hd_eq {q : Nat} {A A' R R' : List Nat} (h1 : A = A') (h2 : R = R') : hd q A R = hd q A' R' := by
  rw [h1, h2]

theorem hdR_eq {q : Nat} {A A' R R' : List Nat} (h1 : A = A') (h2 : R = R') :
    hdR q A R = hdR q A' R' := by
  rw [h1, h2]

theorem mb : ∀ V : List Nat, NoB V → (∃ a ∈ V, a ∈ bits) →
    ∃ p b X, V = List.replicate p 1 ++ b :: X ∧ b ∈ bits ∧ Sym4 X
  | [], _, ⟨_, ha, _⟩ => by cases ha
  | a :: V, hV, ⟨x, hx, hxb⟩ => by
    have ha : a ∈ NB := hV a (List.mem_cons_self ..)
    have hV' : NoB V := fun y hy => hV y (List.mem_cons_of_mem _ hy)
    by_cases h1 : a = 1
    · subst h1
      have hx' : x ∈ V := by
        rcases List.mem_cons.mp hx with e | e
        · subst e; simp [bits] at hxb
        · exact e
      obtain ⟨p, b, X, e, hb, hX⟩ := mb V hV' ⟨x, hx', hxb⟩
      refine ⟨p + 1, b, X, ?_, hb, hX⟩
      subst e
      rfl
    · have hab : a ∈ bits := by
        simp [NB] at ha
        simp [bits]
        omega
      exact ⟨0, a, V, rfl, hab, hV'.sym4⟩

theorem blk_bit (n d : Nat) : ∃ a ∈ blkW n d, a ∈ bits := by
  cases d with
  | zero => exact ⟨2, by simp [blkW], by simp [bits]⟩
  | succ d => exact ⟨3, by simp [blkW], by simp [bits]⟩

theorem fw_bit (n : Nat) : ∀ ds : List Nat, ds ≠ [] → ∃ a ∈ FWr n ds, a ∈ bits
  | [], h => absurd rfl h
  | d :: ds, _ =>
    let ⟨a, ha, hb⟩ := blk_bit n d
    ⟨a, List.mem_append_right _ ha, hb⟩

theorem bitsOf_rev (R : List Bool) : Bits (bitsOf R).reverse :=
  fun a ha => Bits.ofB R a (List.mem_reverse.mp ha)

theorem bits_of_eq {R : List Bool} {R' : List Nat} (h : bitsOf R = R' ++ [2]) : Bits R'.reverse := by
  intro a ha
  have := Bits.ofB R a
  rw [h] at this
  exact this (List.mem_append_left _ (List.mem_reverse.mp ha))

theorem false_of_eq {R : List Bool} {R' : List Nat} (h : bitsOf R = R' ++ [2]) : false ∈ R := by
  have h2 : 2 ∈ bitsOf R := by rw [h]; simp
  obtain ⟨b, hb, e⟩ := List.mem_map.mp h2
  cases b
  · exact hb
  · simp at e

/-! ## Invariants of the code -/

def InvR (R : List Bool) : Prop :=
  false ∈ R ∧ (R.length = 1 → R = [false]) ∧ (R.length = 2 → R.getD 1 true = false)

theorem rot_len (R : List Bool) : (rot R).length = R.length := by
  unfold rot
  simp only [List.length_append, List.length_drop, List.length_take]
  omega

theorem mem_rot {a : Bool} {R : List Bool} (h : a ∈ R) : a ∈ rot R := by
  unfold rot
  generalize (entryOnes R + 3) % R.length = k
  have e := List.take_append_drop k R
  rw [← e] at h
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append_right _ h
  · exact List.mem_append_left _ h

theorem inv_rot {R : List Bool} (h : InvR R) : InvR (rot R) := by
  refine ⟨mem_rot h.1, fun hl => ?_, fun hl => ?_⟩
  · have e := h.2.1 (by rw [← rot_len]; exact hl)
    rw [e]
    decide
  · have hl2 : R.length = 2 := by rw [← rot_len]; exact hl
    have e1 := h.2.2 hl2
    rcases R with _ | ⟨a, _ | ⟨b, _ | ⟨c, R⟩⟩⟩
    · simp at hl2
    · simp at hl2
    · simp at e1
      subst e1
      cases a <;> decide
    · simp at hl2

theorem inv_rotN {R : List Bool} (h : InvR R) : ∀ k, InvR (rotN k R)
  | 0 => h
  | k + 1 => inv_rotN (inv_rot h) k

/-! ## The count-down -/

def cellN : Option Bool → Nat
  | none => 0
  | some false => 2
  | some true => 3

theorem cdn_cases (c : Nat) : cdn c = 0 ∨ cdn c = 2 ∨ cdn c = 3 := by
  unfold cdn
  split <;> simp

theorem cdn_all (c : Nat) : cdn c ∈ ALL := by
  unfold cdn
  split <;> simp [ALL]

/-- One rotation of the count-down. -/
theorem cdStep (R : List Bool) (hR : InvR R) (g : Nat) (Lw V : List Nat) (c : Nat) (hc : c ∈ bits)
    (hL : Bits Lw) (hV : NoB V) (hVb : ∃ a ∈ V, a ∈ bits) :
    ∃ g', 1 ≤ g' ∧ zpBase.Reach
      (hd Q.BK2 ((bitsOf R).reverse ++ List.replicate g 0 ++ 0 :: (Lw ++ [c])) (1 :: V))
      (hd Q.BK2 ((bitsOf (rot R)).reverse ++ List.replicate g' 0 ++ 0 :: (Lw ++ [cdn c])) (1 :: V)) := by
  have hA := segA (bitsOf R).reverse Lw V g c hc (bitsOf_rev R) hL hV
  have hX : Sym4 (List.replicate g 0 ++ 0 :: (Lw ++ cdn c :: 1 :: V)) :=
    (zeros4 g).app (Sym4.cons (by simp [ALL]) (hL.sym4.app (Sym4.cons (cdn_all c)
      (Sym4.cons (by simp [ALL]) hV.sym4))))
  obtain ⟨R', H, hrot, -, -, hr⟩ := rotate rotNormal R hR.1 _ hX
  rw [rst_hd, rnav_hd] at hr
  obtain ⟨p, b, X, rfl, hb, hX'⟩ := mb V hV hVb
  have hB := segB R'.reverse Lw X H.length g p (cdn c) b (cdn_cases c) hb (bits_of_eq hrot) hL hX'
  refine ⟨H.length + g + 1, by omega, hA.trans (hr.trans (hB.of_eq (hdR_eq rfl (by simp only [List.append_assoc])) (hd_eq ?_ rfl)))⟩
  rw [hrot]
  simp [List.replicate_succ, rep_rep]

/-- The whole count-down: `iota` rotations, leaving a blank scanned cell. -/
theorem countdown (R : List Bool) (hR : InvR R) (g : Nat) (hg : 1 ≤ g) (Lw V : List Nat) (x : Option Bool)
    (hL : Bits Lw) (hV : NoB V) (hVb : ∃ a ∈ V, a ∈ bits) :
    ∃ g', 1 ≤ g' ∧ zpBase.Reach
      (hd Q.BK2 ((bitsOf R).reverse ++ List.replicate g 0 ++ 0 :: (Lw ++ [cellN x])) (1 :: V))
      (hd Q.BK2 ((bitsOf (rotN (iota x) R)).reverse ++ List.replicate g' 0 ++ 0 :: (Lw ++ [0])) (1 :: V)) := by
  rcases x with _ | _ | _
  · exact ⟨g, hg, LTM.Reach.refl _ _⟩
  · obtain ⟨g', hg', h⟩ := cdStep R hR g Lw V 2 (by simp [bits]) hL hV hVb
    exact ⟨g', hg', h⟩
  · obtain ⟨g1, _, h1⟩ := cdStep R hR g Lw V 3 (by simp [bits]) hL hV hVb
    obtain ⟨g2, hg2, h2⟩ := cdStep (rot R) (inv_rot hR) g1 Lw V 2 (by simp [bits]) hL hV hVb
    exact ⟨g2, hg2, h1.trans h2⟩

/-! ## Jump tokens -/

theorem tokens (Lw : List Nat) (ch p b : Nat) (X : List Nat) (hL : Bits Lw) (hch : ch = 0 ∨ ch = 2 ∨ ch = 3)
    (hb : b ∈ bits) (hX : Sym4 X) :
    ∀ (t : Nat) (R : List Bool) (R' : List Nat) (a y : Nat), bitsOf R = R' ++ [2] →
      ∃ g', 1 ≤ g' ∧ zpBase.Reach
        (hdR Q.NAV [2] (R'.reverse ++ 0 :: (List.replicate a 0 ++ List.replicate (t + 1) 1 ++
          List.replicate y 0 ++ 0 :: (Lw ++ ch :: 1 :: (List.replicate p 1 ++ b :: X)))))
        (hd Q.BK2 ((bitsOf (rotN t R)).reverse ++ List.replicate g' 0 ++ 0 :: (Lw ++ [ch]))
          (1 :: (List.replicate p 1 ++ b :: X)))
  | 0, R, R', a, y, hR => by
    have h := segE2 R'.reverse Lw X a y p ch b hch hb (bits_of_eq hR) hL hX
    refine ⟨a + y + 1 + 1, by omega, h.of_eq rfl (hd_eq ?_ rfl)⟩
    simp only [rotN]
    rw [hR]
    simp [List.replicate_succ, rep_rep, rep_cons_comm]
  | t + 1, R, R', a, y, hR => by
    have hch4 : ch ∈ ALL := by rcases hch with rfl | rfl | rfl <;> simp [ALL]
    have hXr : Sym4 (Lw ++ ch :: 1 :: (List.replicate p 1 ++ b :: X)) :=
      hL.sym4.app (Sym4.cons hch4 (Sym4.cons (by simp [ALL]) ((ones4 p).app
        (Sym4.cons (by rcases mem_bits hb with rfl | rfl <;> simp [ALL]) hX))))
    have h1 := segE1b R'.reverse (Lw ++ ch :: 1 :: (List.replicate p 1 ++ b :: X)) a y t (bits_of_eq hR) hXr
    have hX'' : Sym4 (0 :: (List.replicate a 0 ++ 1 :: (List.replicate t 1 ++ [0]) ++ List.replicate y 0 ++
        0 :: (Lw ++ ch :: 1 :: (List.replicate p 1 ++ b :: X)))) :=
      Sym4.cons (by simp [ALL]) ((((zeros4 a).app (Sym4.cons (by simp [ALL]) ((ones4 t).app
        (Sym4.cons (by simp [ALL]) Sym4.nil)))).app (zeros4 y)).app (Sym4.cons (by simp [ALL]) hXr))
    obtain ⟨R2, H2, hrot, -, -, hr⟩ := rotate rotNormal R (false_of_eq hR) _ hX''
    rw [rst_hd, rnav_hd] at hr
    obtain ⟨g', hg', ih⟩ := tokens Lw ch p b X hL hch hb hX t (rot R) R2 (H2.length + a + 1) (y + 1) hrot
    refine ⟨g', hg', ?_⟩
    have hrR : (bitsOf R).reverse = 2 :: R'.reverse := by rw [hR]; simp
    refine (h1.of_eq (hdR_eq rfl ?_) (hd_eq hrR.symm rfl)).trans (hr.trans (ih.of_eq (hdR_eq rfl ?_) rfl))
    · simp [List.replicate_succ, rep_cons_comm]
    · simp [List.replicate_succ, rep_rep, rep_cons_comm]

/-! ## The guest tape as a zipper -/

/-- Guest tape: cells left of the head (nearest first), the scanned cell, cells right
of the head (nearest first). -/
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

/-- The cells left of the head, as they sit on the machine tape (right of the scanned cell). -/
def Rw (z : Zp) : List Nat := bitsOf z.Rt

/-- Write `w` and move (right when `d`); a left move at cell 0 stays. -/
def mv : Zp → Bool → Bool → Zp
  | ⟨Rt, _, Lt⟩, w, true => ⟨w :: Rt, Lt.head?, Lt.tail⟩
  | ⟨[], _, Lt⟩, w, false => ⟨[], some w, Lt⟩
  | ⟨r :: Rt, _, Lt⟩, w, false => ⟨Rt, some r, w :: Lt⟩

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
  rcases z with ⟨_ | ⟨r, Rt⟩, c, Lt⟩ <;> cases d
  · rfl
  · show [w] ++ (Lt.head?.toList ++ Lt.tail) = _
    cases Lt <;> rfl
  · show Rt.reverse ++ (r :: w :: Lt) = (r :: Rt).reverse ++ w :: Lt
    simp
  · show (w :: r :: Rt).reverse ++ (Lt.head?.toList ++ Lt.tail) = _
    cases Lt <;> simp

theorem mv_tape {z : Zp} (hz : z.WF) (w d : Bool) :
    (z.mv w d).tape = fun i => if i = z.Rt.length then some w else z.tape i := by
  have e := set_eq z.Rt.reverse z.c z.Lt hz w
  rw [List.length_reverse] at e
  show (fun i => (z.mv w d).list[i]?) = fun i => if i = z.Rt.length then some w else z.list[i]?
  rw [mv_list]
  exact e.symm

theorem mv_len (z : Zp) (w d : Bool) :
    (z.mv w d).Rt.length = if d then z.Rt.length + 1 else z.Rt.length - 1 := by
  rcases z with ⟨_ | ⟨r, Rt⟩, c, Lt⟩ <;> cases d <;> simp [mv]

theorem mv_WF (z : Zp) (w d : Bool) : (z.mv w d).WF := by
  rcases z with ⟨_ | ⟨r, Rt⟩, c, Lt⟩ <;> cases d
  · intro h; cases h
  · intro h
    cases Lt with
    | nil => rfl
    | cons _ _ => cases h
  · intro h; cases h
  · intro h
    cases Lt with
    | nil => rfl
    | cons _ _ => cases h

end Zp

/-! ## Configurations -/

def bn (b : Bool) : Nat := if b then 3 else 2

theorem bn_bits (b : Bool) : bn b ∈ bits := by cases b <;> simp [bn, bits]

theorem bn_cases (b : Bool) : bn b = 0 ∨ bn b = 2 ∨ bn b = 3 := by cases b <;> simp [bn]

theorem cellN_some (b : Bool) : cellN (some b) = bn b := by cases b <;> rfl

theorem bitsOf_cons (b : Bool) (l : List Bool) : bitsOf (b :: l) = bn b :: bitsOf l := rfl

theorem bits3 (a b c : Bool) (rest : List Bool) :
    (bitsOf (a :: b :: c :: rest)).reverse = (bitsOf rest).reverse ++ [bn c, bn b, bn a] := by
  simp [bitsOf, bn]

theorem bits1 (a : Bool) (rest : List Bool) :
    (bitsOf (a :: rest)).reverse = (bitsOf rest).reverse ++ [bn a] := by
  simp [bitsOf, bn]

theorem NoB.cons {b : Nat} {w : List Nat} (hb : b ∈ NB) (hw : NoB w) : NoB (b :: w) := by
  intro a ha
  rcases List.mem_cons.mp ha with e | e
  · rw [e]; exact hb
  · exact hw a e

/-- The step boundary. -/
def Bd (R : List Bool) (g : Nat) (z : Zp) (W F : List Nat) : ZC :=
  hd Q.BK2 ((bitsOf R).reverse ++ List.replicate g 0 ++ 0 :: (z.Lw ++ [cellN z.c]))
    (1 :: (z.Rw ++ 1 :: (W ++ 1 :: F)))

/-- The result state. -/
def RE (o : Bool) (W F : List Nat) : ZC := hdR (dpOf (bn o)) [1] (W ++ 1 :: F)

/-! ## Fuel decrement after the count-down -/

theorem dec (n : Nat) (ds : List Nat) (hds : Dig n ds) (Qw Lw Rw W : List Nat) (g : Nat)
    (hQ : Bits Qw) (hL : Bits Lw) (hR : Bits Rw) (hW : NoB W) :
    (0 < valr n ds → ∃ ds', Dig n ds' ∧ ds'.length = ds.length ∧ valr n ds' + 1 = valr n ds ∧
      zpBase.Reach (hd Q.BK2 (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0])) (1 :: (Rw ++ 1 :: (W ++ 1 :: FWr n ds))))
        (hd Q.FBACK (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0])) (1 :: (Rw ++ 1 :: (W ++ 1 :: FWr n ds'))))) ∧
    (valr n ds = 0 →
      zpBase.Reach (hd Q.BK2 (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0])) (1 :: (Rw ++ 1 :: (W ++ 1 :: FWr n ds))))
        (hd Q.EXH (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0]))
          (1 :: (Rw ++ 1 :: (W ++ 1 :: FWr n (ds.map fun _ => n + 1)))))) := by
  have hC := segC Qw Lw Rw W (FWr n ds) g hQ hL hR hW (FWr_noB n ds)
  have h1 : (1 : Nat) ∈ NB := by simp [NB]
  have hL0 : Sym4 (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0])) :=
    (hQ.sym4.app (zeros4 g)).app (Sym4.cons (by simp [ALL]) (hL.sym4.app (Sym4.cons (by simp [ALL]) Sym4.nil)))
  have hW1 : NoB (1 :: (Rw ++ 1 :: W)) := NoB.cons h1 (hR.noB.app (NoB.cons h1 hW))
  have hLL : Sym4 (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0]) ++ 1 :: (Rw ++ 1 :: W)) := hL0.app hW1.sym4
  have hF := fuel n ds hds _ [] hLL Sym4.nil (Or.inl rfl)
  refine ⟨fun hpos => ?_, fun h0 => ?_⟩
  · obtain ⟨ds', hd', hl, hv, hr⟩ := hF.1 hpos
    have hwk := walkL Q.FBACK (Or.inl rfl) (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0]))
      (1 :: (Rw ++ 1 :: W) ++ [1]) (FWr n ds' ++ []) hL0 (hW1.app (NoB.cons h1 NoB.nil))
      ((FWr_noB n ds').sym4.app Sym4.nil)
    refine ⟨ds', hd', hl, hv, hC.trans (hr.trans (hwk.of_eq (hd_eq ?_ rfl) (hd_eq rfl ?_)))⟩
    · simp only [List.append_assoc]
    · simp
  · have hr := hF.2 h0
    have hwk := walkL Q.EXH (Or.inr rfl) (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0]))
      (1 :: (Rw ++ 1 :: W)) (1 :: (FWr n (ds.map fun _ => n + 1) ++ [])) hL0 hW1
      (Sym4.cons (by simp [ALL]) ((FWr_noB n _).sym4.app Sym4.nil))
    exact hC.trans (hr.trans (hwk.of_eq rfl (hd_eq rfl (by simp))))

/-! ## After a move: record rotation and the jump tokens -/

theorem post (R1 : List Bool) (h0 : false ∈ R1) (Lw2 : List Nat) (ch2 p b : Nat) (X2 : List Nat) (y : Nat)
    (hL : Bits Lw2) (hch : ch2 = 0 ∨ ch2 = 2 ∨ ch2 = 3) (hb : b ∈ bits) (hX2 : Sym4 X2) :
    ∃ g', 1 ≤ g' ∧ zpBase.Reach
      (hd Q.RTW (bitsOf R1).reverse
        (List.replicate y 0 ++ 0 :: (Lw2 ++ ch2 :: 1 :: (List.replicate p 1 ++ b :: X2))))
      (hd Q.BK2 ((bitsOf (rotN (entryOnes R1 + 1) (rot R1))).reverse ++ List.replicate g' 0 ++
        0 :: (Lw2 ++ [ch2])) (1 :: (List.replicate p 1 ++ b :: X2))) := by
  have hch4 : ch2 ∈ ALL := by rcases hch with rfl | rfl | rfl <;> simp [ALL]
  have hb4 : b ∈ ALL := by rcases mem_bits hb with rfl | rfl <;> simp [ALL]
  have hX : Sym4 (List.replicate y 0 ++ 0 :: (Lw2 ++ ch2 :: 1 :: (List.replicate p 1 ++ b :: X2))) :=
    (zeros4 y).app (Sym4.cons (by simp [ALL]) (hL.sym4.app (Sym4.cons hch4 (Sym4.cons (by simp [ALL])
      ((ones4 p).app (Sym4.cons hb4 hX2))))))
  obtain ⟨R', H, hrot, hH, -, hr⟩ := rotate rotRecord R1 h0 _ hX
  rw [rst_hd, rnav_hd, hH] at hr
  obtain ⟨g', hg', ht⟩ := tokens Lw2 ch2 p b X2 hL hch hb hX2 (entryOnes R1 + 1) (rot R1) R' 0 y hrot
  refine ⟨g', hg', hr.trans (ht.of_eq (hdR_eq rfl ?_) rfl)⟩
  simp

/-! ## The peek: halt or write, move and rotate -/

theorem peek (R1 : List Bool) (hR1 : InvR R1) (g : Nat) (hg : 1 ≤ g) (z : Zp) (W F : List Nat)
    (hW : NoB W) (hF : NoB F) (hFb : ∃ a ∈ F, a ∈ bits) :
    (R1.getD 2 false = false → zpBase.Reach
      (hd Q.FBACK ((bitsOf R1).reverse ++ List.replicate g 0 ++ 0 :: (z.Lw ++ [0]))
        (1 :: (z.Rw ++ 1 :: (W ++ 1 :: F))))
      (RE (R1.getD 0 false) W F)) ∧
    (R1.getD 2 false = true → ∃ g', 1 ≤ g' ∧ zpBase.Reach
      (hd Q.FBACK ((bitsOf R1).reverse ++ List.replicate g 0 ++ 0 :: (z.Lw ++ [0]))
        (1 :: (z.Rw ++ 1 :: (W ++ 1 :: F))))
      (Bd (rotN (entryOnes R1 + 1) (rot R1)) g' (z.mv (R1.getD 0 false) (R1.getD 1 false)) W F)) := by
  have hLw : Bits z.Lw := Bits.ofB _
  have hRw : Bits z.Rw := Bits.ofB _
  have h1 : (1 : Nat) ∈ NB := by simp [NB]
  have hW' : NoB (W ++ 1 :: F) := hW.app (NoB.cons h1 hF)
  have hWb : ∃ a ∈ W ++ 1 :: F, a ∈ bits := by
    obtain ⟨a, ha, hab⟩ := hFb
    exact ⟨a, List.mem_append_right _ (List.mem_cons_of_mem _ ha), hab⟩
  rcases R1 with _ | ⟨r0, _ | ⟨r1, _ | ⟨r2, rest⟩⟩⟩
  · exact absurd hR1.1 (by simp)
  · have e := hR1.2.1 rfl
    simp only [List.cons.injEq, and_true] at e
    subst e
    refine ⟨fun _ => ?_, fun h => by simp at h⟩
    exact segShort1 z.Lw z.Rw (W ++ 1 :: F) g hLw hRw hW'
  · have e := hR1.2.2 rfl
    simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] at e
    subst e
    refine ⟨fun _ => ?_, fun h => by simp at h⟩
    have h := segShort2 z.Lw z.Rw (W ++ 1 :: F) g (bn r0) (bn_bits r0) hLw hRw hW'
    exact h.of_eq (hd_eq (by cases r0 <;> rfl) rfl) rfl
  · have hrest : Bits (bitsOf rest).reverse := bitsOf_rev rest
    have hf : false ∈ r0 :: r1 :: r2 :: rest := hR1.1
    refine ⟨fun h2 => ?_, fun h2 => ?_⟩
    · have h2' : r2 = false := h2
      subst h2'
      have h := segHalt (bitsOf rest).reverse z.Lw z.Rw (W ++ 1 :: F) g (bn r0) (bn r1) (bn_bits r0)
        (bn_bits r1) hrest hLw hRw hW'
      exact h.of_eq (hd_eq (by rw [bits3]; rfl) rfl) rfl
    · have h2' : r2 = true := h2
      subst h2'
      have hcode : (bitsOf (r0 :: r1 :: true :: rest)).reverse = (bitsOf rest).reverse ++ [3, bn r1, bn r0] := by
        rw [bits3]; rfl
      show ∃ g', 1 ≤ g' ∧ zpBase.Reach _ (Bd _ g' (z.mv r0 r1) W F)
      rw [hcode]
      rcases z with ⟨Rt, c, Lt⟩
      cases r1 with
      | false =>
        cases Rt with
        | nil =>
          have hm := segMv0e (bitsOf rest).reverse (bitsOf Lt.reverse) (W ++ 1 :: F) g (bn r0) (bn_bits r0)
            hrest hLw hW'
          obtain ⟨p, b, X2, eX, hb, hX2⟩ := mb (1 :: (W ++ 1 :: F)) (NoB.cons h1 hW')
            (let ⟨a, ha, hab⟩ := hWb; ⟨a, List.mem_cons_of_mem _ ha, hab⟩)
          obtain ⟨g', hg', hp⟩ := post (r0 :: false :: true :: rest) hf (bitsOf Lt.reverse) (bn r0) p b X2 g
            hLw (bn_cases r0) hb hX2
          rw [← eX, hcode] at hp
          refine ⟨g', hg', hm.trans (hp.of_eq rfl ?_)⟩
          cases r0 <;> rfl
        | cons r Rt =>
          have hm := segMv0c (bitsOf rest).reverse (bitsOf Lt.reverse) (bitsOf Rt) (W ++ 1 :: F) g (bn r0)
            (bn r) (bn_bits r0) (bn_bits r) hrest hLw (Bits.ofB _) hW'
          obtain ⟨p, b, X2, eX, hb, hX2⟩ := mb (bitsOf Rt ++ 1 :: (W ++ 1 :: F))
            ((Bits.ofB Rt).noB.app (NoB.cons h1 hW'))
            (let ⟨a, ha, hab⟩ := hWb; ⟨a, List.mem_append_right _ (List.mem_cons_of_mem _ ha), hab⟩)
          obtain ⟨g', hg', hp⟩ := post (r0 :: false :: true :: rest) hf (bitsOf Lt.reverse ++ [bn r0]) (bn r)
            p b X2 g (hLw.snoc (bn_bits r0)) (bn_cases r) hb hX2
          rw [← eX, hcode] at hp
          refine ⟨g', hg', (hm.of_eq rfl (hd_eq rfl ?_)).trans (hp.of_eq rfl ?_)⟩
          · simp
          · show _ = hd Q.BK2 ((bitsOf _).reverse ++ _ ++ 0 :: (bitsOf (r0 :: Lt).reverse ++ [cellN (some r)]))
              (1 :: (bitsOf Rt ++ 1 :: (W ++ 1 :: F)))
            rw [cellN_some, List.reverse_cons, bitsOf_snoc]
            rfl
      | true =>
        have hm := segMv1 (bitsOf rest).reverse (bitsOf Lt.reverse) (bitsOf Rt) (W ++ 1 :: F) g (bn r0)
          (bn_bits r0) hrest hLw (Bits.ofB _) hW'
        have hX2 : Sym4 (bitsOf Rt ++ 1 :: (W ++ 1 :: F)) := ((Bits.ofB Rt).noB.app (NoB.cons h1 hW')).sym4
        cases Lt with
        | nil =>
          obtain ⟨g0, rfl⟩ : ∃ g0, g = g0 + 1 := ⟨g - 1, by omega⟩
          obtain ⟨g', hg', hp⟩ := post (r0 :: true :: true :: rest) hf [] 0 0 (bn r0)
            (bitsOf Rt ++ 1 :: (W ++ 1 :: F)) g0 Bits.nil (Or.inl rfl) (bn_bits r0) hX2
          rw [hcode] at hp
          refine ⟨g', hg', (hm.of_eq rfl (hd_eq rfl ?_)).trans (hp.of_eq rfl rfl)⟩
          simp [List.replicate_succ, rep_cons_comm, Zp.Lw, bitsOf]
        | cons x Lt =>
          obtain ⟨g', hg', hp⟩ := post (r0 :: true :: true :: rest) hf (bitsOf Lt.reverse) (bn x) 0 (bn r0)
            (bitsOf Rt ++ 1 :: (W ++ 1 :: F)) g (Bits.ofB _) (bn_cases x) (bn_bits r0) hX2
          rw [hcode] at hp
          refine ⟨g', hg', (hm.of_eq rfl (hd_eq rfl ?_)).trans (hp.of_eq rfl ?_)⟩
          · simp [bitsOf, bn]
          · cases x <;> rfl

/-! ## The whole run -/

theorem runI (n : Nat) (W : List Nat) (hW : NoB W) :
    ∀ T R g z ds, InvR R → 1 ≤ g → z.WF → Dig n ds → ds ≠ [] → valr n ds = T →
      ∃ ds', Dig n ds' ∧ ds'.length = ds.length ∧
        zpBase.Reach (Bd R g z W (FWr n ds)) (RE (runAux T R z.tape z.Rt.length) W (FWr n ds'))
  | T, R, g, z, ds, hR, hg, hz, hds, hne, hv => by
    have h1 : (1 : Nat) ∈ NB := by simp [NB]
    have hV : NoB (z.Rw ++ 1 :: (W ++ 1 :: FWr n ds)) :=
      (Bits.ofB _).noB.app (NoB.cons h1 (hW.app (NoB.cons h1 (FWr_noB n ds))))
    have hVb : ∃ a ∈ z.Rw ++ 1 :: (W ++ 1 :: FWr n ds), a ∈ bits := by
      obtain ⟨a, ha, hab⟩ := fw_bit n ds hne
      exact ⟨a, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_cons_of_mem _ ha))), hab⟩
    obtain ⟨g1, hg1, hcd⟩ := countdown R hR g hg z.Lw _ z.c (Bits.ofB _) hV hVb
    have hR1 : InvR (rotN (iota z.c) R) := inv_rotN hR _
    have hD := dec n ds hds (bitsOf (rotN (iota z.c) R)).reverse z.Lw z.Rw W g1 (bitsOf_rev _)
      (Bits.ofB _) (Bits.ofB _) hW
    cases T with
    | zero =>
      refine ⟨ds.map fun _ => n + 1, fun d hd => ?_, by simp, ?_⟩
      · obtain ⟨_, -, rfl⟩ := List.mem_map.mp hd
        exact Nat.le_refl _
      · have hE := hD.2 hv
        obtain ⟨r, rest, e⟩ : ∃ r rest, rotN (iota z.c) R = r :: rest := by
          cases h : rotN (iota z.c) R with
          | nil => rw [h] at hR1; exact absurd hR1.1 (by simp)
          | cons r rest => exact ⟨r, rest, rfl⟩
        rw [e, bits1] at hE hcd
        have hx := segExh (bitsOf rest).reverse z.Lw z.Rw (W ++ 1 :: FWr n (ds.map fun _ => n + 1)) g1 (bn r)
          (bn_bits r) (bitsOf_rev _) (Bits.ofB _) (Bits.ofB _)
          (hW.app (NoB.cons h1 (FWr_noB n _)))
        exact (hcd.trans (hE.trans hx)).of_eq rfl (by simp [RE, runAux, dpOf, bn])
    | succ T =>
      obtain ⟨ds1, hd1, hl1, hv1, hdec⟩ := hD.1 (by omega)
      have hne1 : ds1 ≠ [] := by
        intro h; rw [h] at hl1; exact hne (List.length_eq_zero_iff.mp hl1.symm)
      have hP := peek (rotN (iota z.c) R) hR1 g1 hg1 z W (FWr n ds1) hW (FWr_noB n ds1) (fw_bit n ds1 hne1)
      simp only [runAux]
      rw [Zp.tape_head hz]
      cases h2 : (rotN (iota z.c) R).getD 2 false with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨ds1, hd1, hl1, hcd.trans (hdec.trans (hP.1 h2))⟩
      | true =>
        simp only [↓reduceIte]
        obtain ⟨g', hg', hm⟩ := hP.2 h2
        obtain ⟨ds2, hd2, hl2, ih⟩ := runI n W hW T _ g' _ ds1
          (inv_rotN (inv_rot hR1) _) hg' (Zp.mv_WF _ _ _) hd1 hne1 (by omega)
        rw [Zp.mv_tape hz, Zp.mv_len] at ih
        exact ⟨ds2, hd2, hl2.trans hl1, hcd.trans (hdec.trans (hm.trans ih))⟩
  termination_by T => T

end ZP
