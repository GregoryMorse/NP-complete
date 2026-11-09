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


/-! ## The switch step -/

theorem _root_.ZP.LTM.Reach.tr {M : LTM} {a b c d : ZC} (h1 : M.Reach a b) (h2 : M.Reach c d)
    (e : b = c) : M.Reach a d := h1.trans (e ▸ h2)

theorem stext_snoc (q : List (List Bool)) (st : List Bool) :
    stext (q ++ [st]) = 1 :: bitsOf st ++ (q.reverse.map stxt).flatten := by
  simp [stext, stxt]

/-- The guest tape after a switch that brings the stack `f` back. -/
def zsw (z : Zp) (f : List Bool) : Zp := ⟨z.Rt, f.reverse.head?, f.reverse.tail⟩

theorem bitsOf_reverse (w : List Bool) : (bitsOf w).reverse = bitsOf w.reverse := by
  simp [bitsOf, List.map_reverse]

theorem Lw_len (z : Zp) : z.Lw.length = z.Lt.length := by
  simp [Zp.Lw, bitsOf]


theorem switchStep (r0 : Bool) (rest : List Bool) (g : Nat) (z : Zp) (W F : List Nat)
    (hW : NoB W) (hF : NoB F) (hFb : ∃ a ∈ F, a ∈ bits) (hf : false ∈ r0 :: true :: false :: rest)
    (f0 : List Bool) (rq : List (List Bool)) (hcap : Cap (f0 :: rq) (g + z.Lw.length)) :
    ∃ g', g + z.Lw.length ≤ g' + (zsw z f0).Lw.length ∧ 1 ≤ g' ∧ zmulLogic.Reach
      (hd Q.FBACK ((bitsOf (r0 :: true :: false :: rest)).reverse ++ List.replicate g 0 ++ 0 :: (z.Lw ++ [0]))
        (1 :: (z.Rw ++ 1 :: (W ++ 1 :: (F ++ 0 :: stext (f0 :: rq))))))
      (Bd (rotN (entryOnes (r0 :: true :: false :: rest) + 1) (rot (r0 :: true :: false :: rest))) g'
        (zsw z f0) W F (stext (rq ++ [z.Lt]))) := by
  have h1' : (1 : Nat) ∈ NB := by simp [NB]
  have hrest : Bits (bitsOf rest).reverse := bitsOf_rev rest
  have hLw : Bits z.Lw := Bits.ofB _
  have hRw : Bits z.Rw := Bits.ofB _
  have hcode : (bitsOf (r0 :: true :: false :: rest)).reverse = (bitsOf rest).reverse ++ [2, 3, bn r0] := by
    rw [bits3]; rfl
  have hST0 : NoB (rq.reverse.map stxt).flatten := by
    have := stext_noB (rq ++ [z.Lt])
    rw [stext_snoc] at this
    intro a ha
    exact this a (List.mem_cons_of_mem _ (List.mem_append_right _ ha))
  rw [hcode, stext_cons, stext_snoc]
  generalize (rq.reverse.map stxt).flatten = ST0 at hST0 ⊢
  have hST : NoB (ST0 ++ 1 :: bitsOf f0) :=
    hST0.app (NoB.cons h1' (Bits.ofB f0).noB)
  have h1 := segSw (bitsOf rest).reverse z.Lw z.Rw W F (ST0 ++ 1 :: bitsOf f0) g (bn r0)
    (mem_bits (bn_bits r0)) hrest hLw hRw hW hF hST
  have hZf : NoB (1 :: (z.Rw ++ 1 :: (W ++ 1 :: F))) :=
    NoB.cons h1' (hRw.noB.app (NoB.cons h1' (hW.app (NoB.cons h1' hF))))
  have hQc : Sym4 ((bitsOf rest).reverse ++ [2, 3, bn r0]) :=
    hrest.sym4.app (Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL])
      (Sym4.cons (by rcases mem_bits (bn_bits r0) with h | h <;> rw [h] <;> simp [ALL]) Sym4.nil)))
  have hcap' : (bitsOf f0).length ≤ g + z.Lw.length + 1 := by
    have := hcap f0 (List.mem_cons_self ..)
    simp [bitsOf] at this ⊢
    omega
  have h2 := switchCore ((bitsOf rest).reverse ++ [2, 3, bn r0]) z.Lw
    (1 :: (z.Rw ++ 1 :: (W ++ 1 :: F))) ST0 (bitsOf f0) g hQc hLw hZf hST0 (Bits.ofB _) hcap'
  have hLwr : z.Lw.reverse = bitsOf z.Lt := by simp [Zp.Lw, bitsOf, List.map_reverse]
  have hV0 : NoB (z.Rw ++ 1 :: (W ++ 1 :: F)) := hRw.noB.app (NoB.cons h1' (hW.app (NoB.cons h1' hF)))
  have hT : Sym4 (0 :: ((1 :: (bitsOf z.Lt ++ ST0)) ++ [0])) :=
    Sym4.cons (by simp [ALL]) ((Sym4.cons (by simp [ALL]) ((Bits.ofB _).sym4.app hST0.sym4)).app Sym4.zero)
  obtain ⟨p, b, X2, hV, hb, hX2⟩ := mb2 _ _ hV0 hT (by
    obtain ⟨a, ha, hab⟩ := hFb
    exact ⟨a, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_cons_of_mem _ ha))), hab⟩)
  rw [hLwr] at h2
  have hZV : Sym4 (z.Rw ++ 1 :: (W ++ 1 :: F) ++ 0 :: ((1 :: (bitsOf z.Lt ++ ST0)) ++ [0])) :=
    hV0.sym4.app hT
  have hcodeS : Sym4 ((bitsOf rest).reverse ++ [2, 3, bn r0]) := hQc
  rcases List.eq_nil_or_concat f0 with rfl | ⟨Lt0, c0, rfl⟩
  · -- the front stack is empty
    have e0 : bitsOf ([] : List Bool) = [] := rfl
    rw [e0] at h1 h2 ⊢
    simp only [List.length_nil, Nat.sub_zero, List.nil_append] at h2 ⊢
    have hRs : Sym4 (0 :: 1 :: (z.Rw ++ 1 :: (W ++ 1 :: F) ++ 0 :: ((1 :: (bitsOf z.Lt ++ ST0)) ++ [0]))) :=
      Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) hZV)
    have h3 := rtwSweep ((bitsOf rest).reverse ++ [2, 3, bn r0]) _ (g + z.Lw.length + 1) hcodeS hRs
    obtain ⟨g', hg', h4⟩ := post (r0 :: true :: false :: rest) hf [] 0 p b X2 (g + z.Lw.length) Bits.nil
      (Or.inl rfl) hb hX2
    have hl : (zsw z []).Lw.length = 0 := by simp [zsw, Zp.Lw, bitsOf]
    refine ⟨g', by omega, by omega, ?_⟩
    rw [hcode] at h4
    have hch := ((h1.tr h2 (by simp)).tr h3 (by simp)).tr (lift h4) ?_
    · refine hch.ofEq ?_ ?_
      · simp
      · rw [← hV]
        have e : 1 :: (z.Rw ++ 1 :: (W ++ 1 :: F) ++ 0 :: (1 :: (bitsOf z.Lt ++ ST0) ++ [0])) =
            (1 :: (z.Rw ++ 1 :: (W ++ 1 :: (F ++ 0 :: (1 :: bitsOf z.Lt ++ ST0))))) ++ List.replicate 1 0 := by
          simp
        rw [e, hd_pad]
        simp [Bd, zsw, Zp.Lw, Zp.Rw, bitsOf, cellN]
    · rw [← hV]
      simp [List.replicate_succ']
  · -- the front stack is `Lt0 ++ [c0]`
    simp only [List.concat_eq_append] at h1 h2 hcap hST ⊢
    have hlen : Lt0.length + 1 ≤ g + z.Lw.length := by
      have := hcap (Lt0 ++ [c0]) (List.mem_cons_self ..)
      simpa using this
    have eb : bitsOf (Lt0 ++ [c0]) = bitsOf Lt0 ++ [bn c0] := by simp [bitsOf, bn]
    have hn : g + z.Lw.length + 1 - (bitsOf (Lt0 ++ [c0])).length = g + z.Lw.length - Lt0.length := by
      simp [bitsOf]
    rw [hn] at h2
    have hRs : Sym4 (0 :: (bitsOf Lt0 ++ bn c0 :: 1 :: (z.Rw ++ 1 :: (W ++ 1 :: F) ++
        0 :: ((1 :: (bitsOf z.Lt ++ ST0)) ++ [0])))) :=
      Sym4.cons (by simp [ALL]) (((Bits.ofB Lt0).sym4).app (Sym4.cons (by
        rcases mem_bits (bn_bits c0) with h | h <;> rw [h] <;> simp [ALL])
        (Sym4.cons (by simp [ALL]) hZV)))
    have h3 := rtwSweep ((bitsOf rest).reverse ++ [2, 3, bn r0]) _ (g + z.Lw.length - Lt0.length) hcodeS hRs
    obtain ⟨g', hg', h4⟩ := post (r0 :: true :: false :: rest) hf (bitsOf Lt0) (bn c0) p b X2
      (g + z.Lw.length - Lt0.length) (Bits.ofB _) (bn_cases c0) hb hX2
    have hl : (zsw z (Lt0 ++ [c0])).Lw.length = Lt0.length := by simp [zsw, Zp.Lw, bitsOf]
    refine ⟨g', by omega, by omega, ?_⟩
    rw [hcode] at h4
    have hch := ((h1.tr h2 (by simp)).tr h3 (by simp [eb])).tr (lift h4) ?_
    · refine hch.ofEq ?_ ?_
      · simp
      · rw [← hV]
        have e : 1 :: (z.Rw ++ 1 :: (W ++ 1 :: F) ++ 0 :: (1 :: (bitsOf z.Lt ++ ST0) ++ [0])) =
            (1 :: (z.Rw ++ 1 :: (W ++ 1 :: (F ++ 0 :: (1 :: bitsOf z.Lt ++ ST0))))) ++ List.replicate 1 0 := by
          simp
        rw [e, hd_pad]
        have hzLw : (zsw z (Lt0 ++ [c0])).Lw = bitsOf Lt0 := by simp [zsw, Zp.Lw, bitsOf]
        have hzc : (zsw z (Lt0 ++ [c0])).c = some c0 := by simp [zsw]
        have hzRw : (zsw z (Lt0 ++ [c0])).Rw = z.Rw := rfl
        simp only [Bd, hzLw, hzc, hzRw, cellN_some]
    · rw [← hV]

/-! ## The peek: halt, or write, move and rotate -/

/-- The result state of a proper halt (`o = true`: the output check starts) or a failure. -/
def REn (o : Bool) (Rw W F ST : List Nat) : ZC :=
  if o then hdR QMul.mK1 [2] (Rw ++ 1 :: (W ++ 1 :: (F ++ 0 :: ST)))
  else hdR (dpOf 2) [1] (W ++ 1 :: (F ++ 0 :: ST))

theorem peekH (R1 : List Bool) (hR1 : InvR R1) (g : Nat) (z : Zp) (W F ST : List Nat)
    (hW : NoB W) (hF : NoB F) (hS : NoB ST) (h2 : R1.getD 2 false = false)
    (h1 : R1.getD 1 false = false) :
    zmulLogic.Reach
      (hd Q.FBACK ((bitsOf R1).reverse ++ List.replicate g 0 ++ 0 :: (z.Lw ++ [0]))
        (1 :: (z.Rw ++ 1 :: (W ++ 1 :: (F ++ 0 :: ST)))))
      (REn (R1.getD 0 false) z.Rw W F ST) := by
  have hLw : Bits z.Lw := Bits.ofB _
  have hRw : Bits z.Rw := Bits.ofB _
  have hW' : Sym4 (W ++ 1 :: (F ++ 0 :: ST)) :=
    hW.sym4.app (Sym4.cons (by simp [ALL]) (hF.sym4.app (Sym4.cons (by simp [ALL]) hS.sym4)))
  have hdp : dpOf 2 = Q.DP10 := rfl
  rcases R1 with _ | ⟨r0, _ | ⟨r1, _ | ⟨r2, rest⟩⟩⟩
  · exact absurd hR1.1 (by simp)
  · have e := hR1.2.1 rfl
    simp only [List.cons.injEq, and_true] at e
    subst e
    have h := lift (segShort1 z.Lw z.Rw _ g hLw hRw hW')
    simpa [REn, hdp, bitsOf, bn] using h
  · have e := hR1.2.2 rfl
    simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] at e
    subst e
    cases r0
    · have h := lift (segShort2_0 z.Lw z.Rw _ g hLw hRw hW')
      simpa [REn, hdp, bitsOf, bn] using h
    · have h := segShort2_1 z.Lw z.Rw _ g hLw hRw hW'
      simpa [REn, bitsOf, bn] using h
  · have hrest : Bits (bitsOf rest).reverse := bitsOf_rev rest
    have h2' : r2 = false := h2
    have h1' : r1 = false := h1
    subst h2' h1'
    have hcode : (bitsOf (r0 :: false :: false :: rest)).reverse = (bitsOf rest).reverse ++ [2, 2, bn r0] := by
      rw [bits3]; rfl
    rw [hcode]
    cases r0
    · have h := lift (segHalt0 (bitsOf rest).reverse z.Lw z.Rw _ g hrest hLw hRw hW')
      simpa [REn, hdp, bn] using h
    · have h := segHalt1 (bitsOf rest).reverse z.Lw z.Rw _ g hrest hLw hRw hW'
      simpa [REn, bn] using h

theorem peekN (R1 : List Bool) (hR1 : InvR R1) (g : Nat) (z : Zp) (W F ST : List Nat)
    (hW : NoB W) (hF : NoB F) (hS : NoB ST) (hFb : ∃ a ∈ F, a ∈ bits) (hg : 1 ≤ g) (h2 : R1.getD 2 false = true) :
    ∃ g', g + z.Lw.length ≤ g' + (z.mv (R1.getD 0 false) (R1.getD 1 false)).Lw.length ∧ 1 ≤ g' ∧
      zmulLogic.Reach
        (hd Q.FBACK ((bitsOf R1).reverse ++ List.replicate g 0 ++ 0 :: (z.Lw ++ [0]))
          (1 :: (z.Rw ++ 1 :: (W ++ 1 :: (F ++ 0 :: ST)))))
        (Bd (rotN (entryOnes R1 + 1) (rot R1)) g' (z.mv (R1.getD 0 false) (R1.getD 1 false)) W F ST) := by
  have hLw : Bits z.Lw := Bits.ofB _
  have hRw : Bits z.Rw := Bits.ofB _
  have h1 : (1 : Nat) ∈ NB := by simp [NB]
  have hWn : NoB (W ++ 1 :: F) := hW.app (NoB.cons h1 hF)
  have hT : Sym4 (0 :: ST) := Sym4.cons (by simp [ALL]) hS.sym4
  have hW' : Sym4 (W ++ 1 :: (F ++ 0 :: ST)) :=
    hW.sym4.app (Sym4.cons (by simp [ALL]) (hF.sym4.app hT))
  have hWb : ∃ a ∈ W ++ 1 :: F, a ∈ bits := by
    obtain ⟨a, ha, hab⟩ := hFb
    exact ⟨a, List.mem_append_right _ (List.mem_cons_of_mem _ ha), hab⟩
  rcases R1 with _ | ⟨r0, _ | ⟨r1, _ | ⟨r2, rest⟩⟩⟩
  · exact absurd hR1.1 (by simp)
  · simp at h2
  · simp at h2
  · have hrest : Bits (bitsOf rest).reverse := bitsOf_rev rest
    have hf : false ∈ r0 :: r1 :: r2 :: rest := hR1.1
    have h2' : r2 = true := h2
    subst h2'
    have hcode : (bitsOf (r0 :: r1 :: true :: rest)).reverse = (bitsOf rest).reverse ++ [3, bn r1, bn r0] := by
      rw [bits3]; rfl
    rw [hcode]
    have hLz : ∀ (Lt : List Bool), (bitsOf Lt).length = Lt.length := fun Lt => by simp [bitsOf]
    rcases z with ⟨Rt, c, Lt⟩
    cases r1 with
    | false =>
      cases Rt with
      | nil =>
        have hm := segMv0e (bitsOf rest).reverse (bitsOf Lt.reverse) _ g (bn r0) (bn_bits r0)
          hrest hLw hW'
        obtain ⟨p, b, X2, eX, hb, hX2⟩ := mb2 (1 :: (W ++ 1 :: F)) (0 :: ST) (NoB.cons h1 hWn) hT
          (let ⟨a, ha, hab⟩ := hWb; ⟨a, List.mem_cons_of_mem _ ha, hab⟩)
        obtain ⟨g', hg', hp⟩ := post (r0 :: false :: true :: rest) hf (bitsOf Lt.reverse) (bn r0) p b X2 g
          hLw (bn_cases r0) hb hX2
        rw [← eX, hcode] at hp
        refine ⟨g', ?_, by omega, ?_⟩
        · simp [Zp.mv, Zp.Lw, bitsOf] at hLw ⊢; omega
        · refine ((lift hm).tr (lift hp) (hd_eq (by simp [bn]) (by simp))).ofEq rfl ?_
          cases r0 <;> simp [Bd, Zp.mv, Zp.Lw, Zp.Rw, bitsOf, cellN, bn]
      | cons r Rt =>
        have hm := segMv0c (bitsOf rest).reverse (bitsOf Lt.reverse) (bitsOf Rt) _ g (bn r0) (bn r)
          (bn_bits r0) (bn_bits r) hrest hLw (Bits.ofB _) hW'
        obtain ⟨p, b, X2, eX, hb, hX2⟩ := mb2 (bitsOf Rt ++ 1 :: (W ++ 1 :: F)) (0 :: ST)
          ((Bits.ofB Rt).noB.app (NoB.cons h1 hWn)) hT
          (let ⟨a, ha, hab⟩ := hWb; ⟨a, List.mem_append_right _ (List.mem_cons_of_mem _ ha), hab⟩)
        obtain ⟨g', hg', hp⟩ := post (r0 :: false :: true :: rest) hf (bitsOf Lt.reverse ++ [bn r0]) (bn r)
          p b X2 g (hLw.snoc (bn_bits r0)) (bn_cases r) hb hX2
        rw [← eX, hcode] at hp
        refine ⟨g', ?_, by omega, ?_⟩
        · simp [Zp.mv, Zp.Lw, bitsOf] at hLw ⊢; omega
        · refine ((lift hm).tr (lift hp) (hd_eq (by simp [bn]) (by simp))).ofEq rfl ?_
          cases r0 <;> cases r <;> simp [Bd, Zp.mv, Zp.Lw, Zp.Rw, bitsOf, cellN, bn, List.reverse_cons]
    | true =>
      have hm := segMv1 (bitsOf rest).reverse (bitsOf Lt.reverse) (bitsOf Rt) _ g (bn r0)
        (bn_bits r0) hrest hLw (Bits.ofB _) hW'
      have hX2 : Sym4 (bitsOf Rt ++ 1 :: (W ++ 1 :: (F ++ 0 :: ST))) :=
        (Bits.ofB Rt).sym4.app (Sym4.cons (by simp [ALL]) hW')
      cases Lt with
      | nil =>
        obtain ⟨g0, rfl⟩ : ∃ g0, g = g0 + 1 := ⟨g - 1, by omega⟩
        obtain ⟨g', hg', hp⟩ := post (r0 :: true :: true :: rest) hf [] 0 0 (bn r0)
          (bitsOf Rt ++ 1 :: (W ++ 1 :: (F ++ 0 :: ST))) g0 Bits.nil (Or.inl rfl) (bn_bits r0) hX2
        rw [hcode] at hp
        refine ⟨g', ?_, by omega, ?_⟩
        · simp [Zp.mv, Zp.Lw, bitsOf] at hLw ⊢; omega
        · refine ((lift hm).tr (lift hp) (hd_eq (by simp [bn]) (by simp [List.replicate_succ, rep_cons_comm, Zp.Lw, bitsOf]))).ofEq rfl ?_
          cases r0 <;> simp [Bd, Zp.mv, Zp.Lw, Zp.Rw, bitsOf, cellN, bn]
      | cons x Lt =>
        obtain ⟨g', hg', hp⟩ := post (r0 :: true :: true :: rest) hf (bitsOf Lt.reverse) (bn x) 0 (bn r0)
          (bitsOf Rt ++ 1 :: (W ++ 1 :: (F ++ 0 :: ST))) g (Bits.ofB _) (bn_cases x) (bn_bits r0) hX2
        rw [hcode] at hp
        refine ⟨g', ?_, by omega, ?_⟩
        · simp [Zp.mv, Zp.Lw, bitsOf] at hLw ⊢; omega
        · refine ((lift hm).tr (lift hp) (hd_eq (by simp [bn]) (by simp [bitsOf, bn]))).ofEq rfl ?_
          cases r0 <;> cases x <;> simp [Bd, Zp.mv, Zp.Lw, Zp.Rw, bitsOf, cellN, bn]

end ZP.Mul
