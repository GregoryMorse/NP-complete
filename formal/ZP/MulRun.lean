module

public import ZP.MulSwitch
public import ZP.MulInterp
public import ZP.MulFuel
public import ZP.ExtChecks

@[expose] public section

/-!
# Z_MUL: a whole guest run (`runMulAux`) on `zmulLogic`

Copy of `Run.lean` for the multiplication machine: the fuel is mixed-width, the tape right of the
fuel carries the storage `0 :: ST`, the room `g + |Lw|` never decreases, and the switch step
moves stacks between the tape and the storage.
-/

namespace ZP.Mul

open ZP

theorem lift {c c' : ZC} (h : zmBase.Reach c c') : zmulLogic.Reach c c' :=
  ZP.zmBase_ext_zmulLogic.reach h

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

theorem _root_.ZP.LTM.Reach.ofEq {M : LTM} {c1 c2 c3 c4 : ZC} (h : M.Reach c1 c2) (e1 : c1 = c3) (e2 : c2 = c4) :
    M.Reach c3 c4 := e1 ▸ e2 ▸ h

theorem hd_eq {q : Nat} {A A' R R' : List Nat} (h1 : A = A') (h2 : R = R') : hd q A R = hd q A' R' := by
  rw [h1, h2]

theorem hdR_eq {q : Nat} {A A' R R' : List Nat} (h1 : A = A') (h2 : R = R') :
    hdR q A R = hdR q A' R' := by
  rw [h1, h2]


theorem mb2 : ∀ V T : List Nat, NoB V → Sym4 T → (∃ a ∈ V, a ∈ bits) →
    ∃ p b X, V ++ T = List.replicate p 1 ++ b :: X ∧ b ∈ bits ∧ Sym4 X
  | [], _, _, _, ⟨_, ha, _⟩ => by cases ha
  | a :: V, T, hV, hT, ⟨x, hx, hxb⟩ => by
    have ha : a ∈ NB := hV a (List.mem_cons_self ..)
    have hV' : NoB V := fun y hy => hV y (List.mem_cons_of_mem _ hy)
    by_cases h1 : a = 1
    · subst h1
      have hx' : x ∈ V := by
        rcases List.mem_cons.mp hx with e | e
        · subst e; simp [bits] at hxb
        · exact e
      obtain ⟨p, b, X, e, hb, hX⟩ := mb2 V T hV' hT ⟨x, hx', hxb⟩
      refine ⟨p + 1, b, X, ?_, hb, hX⟩
      show 1 :: (V ++ T) = _
      rw [e]
      rfl
    · have hab : a ∈ bits := by
        simp [NB] at ha
        simp [bits]
        omega
      exact ⟨0, a, V ++ T, rfl, hab, hV'.sym4.app hT⟩

theorem blk_bit (n d : Nat) : ∃ a ∈ blkW n d, a ∈ bits := by
  cases d with
  | zero => exact ⟨2, by simp [blkW], by simp [bits]⟩
  | succ d => exact ⟨3, by simp [blkW], by simp [bits]⟩

theorem fw_bit : ∀ ds : List Dg, ds ≠ [] → ∃ a ∈ FWr ds, a ∈ bits
  | [], h => absurd rfl h
  | (n, d) :: ds, _ =>
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

/-- One rotation of the count-down. -/
theorem cdStep (R : List Bool) (hR : InvR R) (g : Nat) (Lw V : List Nat) (c : Nat) (hc : c ∈ bits)
    (hL : Bits Lw) (hV : Sym4 V)
    (hVd : ∃ p b X, V = List.replicate p 1 ++ b :: X ∧ b ∈ bits ∧ Sym4 X) :
    ∃ g', g ≤ g' ∧ zmBase.Reach
      (hd Q.BK2 ((bitsOf R).reverse ++ List.replicate g 0 ++ 0 :: (Lw ++ [c])) (1 :: V))
      (hd Q.BK2 ((bitsOf (rot R)).reverse ++ List.replicate g' 0 ++ 0 :: (Lw ++ [cdn c])) (1 :: V)) := by
  have hA := segA (bitsOf R).reverse Lw V g c hc (bitsOf_rev R) hL hV
  have hX : Sym4 (List.replicate g 0 ++ 0 :: (Lw ++ cdn c :: 1 :: V)) :=
    (zeros4 g).app (Sym4.cons (by simp [ALL]) (hL.sym4.app (Sym4.cons (cdn_all c)
      (Sym4.cons (by simp [ALL]) hV))))
  obtain ⟨R', H, hrot, -, -, hr⟩ := rotate rotNormal R hR.1 _ hX
  rw [rst_hd, rnav_hd] at hr
  obtain ⟨p, b, X, rfl, hb, hX'⟩ := hVd
  have hB := segB R'.reverse Lw X H.length g p (cdn c) b (cdn_cases c) hb (bits_of_eq hrot) hL hX'
  refine ⟨H.length + g + 1, by omega, hA.trans (hr.trans (hB.ofEq (hdR_eq rfl (by simp only [List.append_assoc])) (hd_eq ?_ rfl)))⟩
  rw [hrot]
  simp [List.replicate_succ, rep_rep]

/-- The whole count-down: `iota` rotations, leaving a blank scanned cell. -/
theorem countdown (R : List Bool) (hR : InvR R) (g : Nat) (hg : 1 ≤ g) (Lw V : List Nat) (x : Option Bool)
    (hL : Bits Lw) (hV : Sym4 V)
    (hVd : ∃ p b X, V = List.replicate p 1 ++ b :: X ∧ b ∈ bits ∧ Sym4 X) :
    ∃ g', g ≤ g' ∧ zmBase.Reach
      (hd Q.BK2 ((bitsOf R).reverse ++ List.replicate g 0 ++ 0 :: (Lw ++ [cellN x])) (1 :: V))
      (hd Q.BK2 ((bitsOf (rotN (iota x) R)).reverse ++ List.replicate g' 0 ++ 0 :: (Lw ++ [0])) (1 :: V)) := by
  rcases x with _ | _ | _
  · exact ⟨g, Nat.le_refl _, LTM.Reach.refl _ _⟩
  · obtain ⟨g', hg', h⟩ := cdStep R hR g Lw V 2 (by simp [bits]) hL hV hVd
    exact ⟨g', hg', h⟩
  · obtain ⟨g1, hg1, h1⟩ := cdStep R hR g Lw V 3 (by simp [bits]) hL hV hVd
    obtain ⟨g2, hg2, h2⟩ := cdStep (rot R) (inv_rot hR) g1 Lw V 2 (by simp [bits]) hL hV hVd
    exact ⟨g2, Nat.le_trans hg1 hg2, h1.trans h2⟩

/-! ## Jump tokens -/

theorem tokens (Lw : List Nat) (ch p b : Nat) (X : List Nat) (hL : Bits Lw) (hch : ch = 0 ∨ ch = 2 ∨ ch = 3)
    (hb : b ∈ bits) (hX : Sym4 X) :
    ∀ (t : Nat) (R : List Bool) (R' : List Nat) (a y : Nat), bitsOf R = R' ++ [2] →
      ∃ g', y + 2 ≤ g' ∧ zmBase.Reach
        (hdR Q.NAV [2] (R'.reverse ++ 0 :: (List.replicate a 0 ++ List.replicate (t + 1) 1 ++
          List.replicate y 0 ++ 0 :: (Lw ++ ch :: 1 :: (List.replicate p 1 ++ b :: X)))))
        (hd Q.BK2 ((bitsOf (rotN t R)).reverse ++ List.replicate g' 0 ++ 0 :: (Lw ++ [ch]))
          (1 :: (List.replicate p 1 ++ b :: X)))
  | 0, R, R', a, y, hR => by
    have h := segE2 R'.reverse Lw X a y p ch b hch hb (bits_of_eq hR) hL hX
    refine ⟨a + y + 1 + 1, by omega, h.ofEq rfl (hd_eq ?_ rfl)⟩
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
    refine ⟨g', by omega, ?_⟩
    have hrR : (bitsOf R).reverse = 2 :: R'.reverse := by rw [hR]; simp
    refine (h1.ofEq (hdR_eq rfl ?_) (hd_eq hrR.symm rfl)).trans (hr.trans (ih.ofEq (hdR_eq rfl ?_) rfl))
    · simp [List.replicate_succ, rep_cons_comm]
    · simp [List.replicate_succ, rep_rep, rep_cons_comm]

/-! ## The guest tape as a zipper -/

/-! ## After a move: record rotation and the jump tokens -/

theorem post (R1 : List Bool) (h0 : false ∈ R1) (Lw2 : List Nat) (ch2 p b : Nat) (X2 : List Nat) (y : Nat)
    (hL : Bits Lw2) (hch : ch2 = 0 ∨ ch2 = 2 ∨ ch2 = 3) (hb : b ∈ bits) (hX2 : Sym4 X2) :
    ∃ g', y + 2 ≤ g' ∧ zmBase.Reach
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
  refine ⟨g', hg', hr.trans (ht.ofEq (hdR_eq rfl ?_) rfl)⟩
  simp

/-! ## The peek: halt or write, move and rotate -/

/-! ## Fuel: to the last fuel cell and decrement -/

theorem segC' (Qw Lw Rw W F ST : List Nat) (g : Nat) (hQ : Bits Qw) (hL : Bits Lw) (hR : Bits Rw)
    (hW : NoB W) (hF : NoB F) (hS : NoB ST) :
    zmBase.Reach (hd Q.BK2 (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0]))
        (1 :: (Rw ++ 1 :: (W ++ 1 :: (F ++ 0 :: ST)))))
      (hd Q.DEC1 (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0]) ++ 1 :: (Rw ++ 1 :: W) ++ [1] ++ F)
        (0 :: ST)) := by
  have hv : Valid swsets [Qw, List.replicate g 0, Lw, Rw, W, F, ST] :=
    Valid.cons hQ (Valid.cons (zeros4 g) (Valid.cons hL (Valid.cons hR (Valid.cons hW
      (Valid.cons hF (Valid.cons hS (Valid.nil _)))))))
  exact checkTT (env := [Qw, List.replicate g 0, Lw, Rw, W, F, ST]) (E := []) (k := 12) hv trivial
    (ls := [.blk 0 .id, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0])
    (rs := [.sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id, .sym 0, .blk 6 .id])
    (ls' := [.blk 0 .id, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0, .sym 1, .blk 3 .id, .sym 1,
      .blk 4 .id, .sym 1, .blk 5 .id]) (rs' := [.sym 0, .blk 6 .id])
    (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)

theorem dec (ds : List Dg) (hds : Dig ds) (Qw Lw Rw W ST : List Nat) (g : Nat)
    (hQ : Bits Qw) (hL : Bits Lw) (hR : Bits Rw) (hW : NoB W) (hS : NoB ST) :
    (0 < valr ds → ∃ ds', Dig ds' ∧ ds'.map Prod.fst = ds.map Prod.fst ∧ valr ds' + 1 = valr ds ∧
      zmBase.Reach (hd Q.BK2 (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0]))
          (1 :: (Rw ++ 1 :: (W ++ 1 :: (FWr ds ++ 0 :: ST)))))
        (hd Q.FBACK (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0]))
          (1 :: (Rw ++ 1 :: (W ++ 1 :: (FWr ds' ++ 0 :: ST)))))) ∧
    (valr ds = 0 →
      zmBase.Reach (hd Q.BK2 (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0]))
          (1 :: (Rw ++ 1 :: (W ++ 1 :: (FWr ds ++ 0 :: ST)))))
        (hd Q.EXH (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0]))
          (1 :: (Rw ++ 1 :: (W ++ 1 :: (FWr (full ds) ++ 0 :: ST)))))) := by
  have hC := segC' Qw Lw Rw W (FWr ds) ST g hQ hL hR hW (FWr_noB ds) hS
  have h1 : (1 : Nat) ∈ NB := by simp [NB]
  have hL0 : Sym4 (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0])) :=
    (hQ.sym4.app (zeros4 g)).app (Sym4.cons (by simp [ALL]) (hL.sym4.app (Sym4.cons (by simp [ALL]) Sym4.nil)))
  have hW1 : NoB (1 :: (Rw ++ 1 :: W)) := NoB.cons h1 (hR.noB.app (NoB.cons h1 hW))
  have hLL : Sym4 (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0]) ++ 1 :: (Rw ++ 1 :: W)) := hL0.app hW1.sym4
  have hT : Sym4 (0 :: ST) := Sym4.cons (by simp [ALL]) hS.sym4
  have hF := fuel ds hds _ (0 :: ST) hLL hT (Or.inr (Or.inr ⟨ST, rfl⟩))
  refine ⟨fun hpos => ?_, fun h0 => ?_⟩
  · obtain ⟨ds', hd', hl, hv, hr⟩ := hF.1 hpos
    have hwk := walkL Q.FBACK (Or.inl rfl) (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0]))
      (1 :: (Rw ++ 1 :: W) ++ [1]) (FWr ds' ++ 0 :: ST) hL0 (hW1.app (NoB.cons h1 NoB.nil))
      ((FWr_noB ds').sym4.app hT)
    refine ⟨ds', hd', hl, hv, hC.trans (hr.trans (hwk.ofEq (hd_eq ?_ rfl) (hd_eq rfl ?_)))⟩
    · simp only [List.append_assoc]
    · simp
  · have hr := hF.2 h0
    have hwk := walkL Q.EXH (Or.inr rfl) (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0]))
      (1 :: (Rw ++ 1 :: W)) (1 :: (FWr (full ds) ++ 0 :: ST)) hL0 hW1
      (Sym4.cons (by simp [ALL]) ((FWr_noB _).sym4.app hT))
    exact hC.trans (hr.trans (hwk.ofEq rfl (hd_eq rfl (by simp))))



/-! ## Streams: blank padding -/

theorem hd_eq' (q : Nat) (A R : List Nat) :
    hd q A R = ⟨q, stail (sapp A.reverse blank), scons (sapp A.reverse blank 0) (sapp R blank)⟩ := by
  show (⟨q, stail (sapp (dL [A, R] [.blk 0 .id]) blank),
    scons (sapp (dL [A, R] [.blk 0 .id]) blank 0) (sapp (dR [A, R] [.blk 1 .id]) blank)⟩ : ZC) = _
  rw [dW_blk0, dW_blk1]

theorem sapp_zeros' (g : Nat) : sapp (List.replicate g 0) blank = blank := by
  induction g with
  | zero => rfl
  | succ g ih =>
    show scons 0 (sapp (List.replicate g 0) blank) = blank
    rw [ih, scons_blank]

theorem hd_pad (q : Nat) (A R : List Nat) (z : Nat) : hd q A (R ++ List.replicate z 0) = hd q A R := by
  rw [hd_eq', hd_eq', sapp_append, sapp_zeros']

/-! ## Storage, capacity, boundary -/

/-- The text of one stack: a marker `M` and its cells. -/
def stxt (st : List Bool) : List Nat := 1 :: bitsOf st

/-- The storage text of the queue: the back stack first, the front stack last. -/
def stext (q : List (List Bool)) : List Nat := (q.reverse.map stxt).flatten

def Cap (q : List (List Bool)) (ρ : Nat) : Prop := ∀ f ∈ q, f.length ≤ ρ

theorem Cap.mono {q : List (List Bool)} {a b : Nat} (h : Cap q a) (hab : a ≤ b) : Cap q b :=
  fun f hf => Nat.le_trans (h f hf) hab

theorem stext_cons (f : List Bool) (rest : List (List Bool)) :
    stext (f :: rest) = (rest.reverse.map stxt).flatten ++ 1 :: bitsOf f := by
  simp [stext, stxt]

theorem stext_noB (q : List (List Bool)) : NoB (stext q) := by
  intro a ha
  simp only [stext, List.mem_flatten, List.mem_map, List.mem_reverse] at ha
  obtain ⟨_, ⟨f, _, rfl⟩, ha⟩ := ha
  simp only [stxt, List.mem_cons] at ha
  rcases ha with rfl | ha
  · simp [NB]
  · have := Bits.ofB f a ha
    rcases mem_bits this with rfl | rfl <;> simp [NB]

/-- The step boundary. -/
def Bd (R : List Bool) (g : Nat) (z : Zp) (W F ST : List Nat) : ZC :=
  hd Q.BK2 ((bitsOf R).reverse ++ List.replicate g 0 ++ 0 :: (z.Lw ++ [cellN z.c]))
    (1 :: (z.Rw ++ 1 :: (W ++ 1 :: (F ++ 0 :: ST))))

theorem rtwSweep (A R : List Nat) (n : Nat) (hA : Sym4 A) (hR : Sym4 R) :
    zmulLogic.Reach (hd Q.RTW (A ++ List.replicate n 0) R) (hd Q.RTW A (List.replicate n 0 ++ R)) := by
  have hv : Valid [ALL, ALL, ALL] [A, List.replicate n 0, R] :=
    Valid.cons hA (Valid.cons (zeros4 n) (Valid.cons hR (Valid.nil _)))
  exact checkTT (env := [A, List.replicate n 0, R]) (E := []) (k := 6) hv trivial
    (ls := [.blk 0 .id, .blk 1 (.const 0)]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id]) (rs' := [.blk 1 (.const 0), .blk 2 .id])
    (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)

end ZP.Mul
