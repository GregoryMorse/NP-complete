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
    ∃ g', 1 ≤ g' ∧ zpLogic.Reach
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
    ∃ g', 1 ≤ g' ∧ zpLogic.Reach
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
      ∃ g', 1 ≤ g' ∧ zpLogic.Reach
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

end ZP
