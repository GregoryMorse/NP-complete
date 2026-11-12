module

public import ZP.MHRunSeg

@[expose] public section

/-!
# Multihead run (shared by `Z_LP` and `Z_LNL`)

The run of a multihead program `P` on an input `x`, on the machine tape

    Q  0^g  0  c  H  M_g  W  M_3  F  0  S        (F = the fuel odometer, S = `storeOf x pos cur`)

(`Q` = the rotated code, `c` = the scanned symbol, see `ZP/MHStore.lean`). Everything is stated for
`mhBase`, hence for every machine `L` with `mhBase.Ext L`. The structure follows `ZP/Run.lean` (the zp2
run, with the guest tape as a zipper); here the guest cells are replaced by the storage.

* `cdStep` / `countdown`: the count-down of the code by the scanned symbol (`iota`);
* `dec`: the fuel decrement (`DEC1`/`FBACK`), time-out (`EXH`);
* `tokens` / `post`: the record rotation and the jump tokens;
* `peek`, `mhStep`: halt, or `GH w d` and the act of `ZP/MHAct.lean`;
* `runMHI`: the whole run, by induction on the fuel.
-/

namespace ZP.MH

open ZP


/-! ## Small facts -/

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


theorem cdn_cases (c : Nat) : cdn c = 0 ∨ cdn c = 2 ∨ cdn c = 3 := by
  unfold cdn
  split <;> simp

theorem cdn_all (c : Nat) : cdn c ∈ ALL := by
  unfold cdn
  split <;> simp [ALL]

/-! ## Jump tokens -/

theorem tokens (Lw : List Nat) (ch p b : Nat) (X : List Nat) (hL : Bits Lw) (hch : ch = 0 ∨ ch = 2 ∨ ch = 3)
    (hb : b ∈ bits) (hX : Sym4 X) :
    ∀ (t : Nat) (R : List Bool) (R' : List Nat) (a y : Nat), bitsOf R = R' ++ [2] →
      ∃ g', 1 ≤ g' ∧ mhBase.Reach
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
    refine ⟨g', hg', ?_⟩
    have hrR : (bitsOf R).reverse = 2 :: R'.reverse := by rw [hR]; simp
    refine (h1.ofEq (hdR_eq rfl ?_) (hd_eq hrR.symm rfl)).trans (hr.trans (ih.ofEq (hdR_eq rfl ?_) rfl))
    · simp [List.replicate_succ, rep_cons_comm]
    · simp [List.replicate_succ, rep_rep, rep_cons_comm]

/-! ## The count-down -/

/-- One rotation of the count-down: `c` is a bit; the code rotates, `c` loses its low bit. `Y` is the part of
the tape right of `H` that has no blank (it contains a bit); `E` is the rest (fuel's end and storage). -/
theorem cdStep (R : List Bool) (hR : InvR R) (g : Nat) (Y E : List Nat) (c : Nat) (hc : c ∈ bits)
    (hY : NoB Y) (hYb : ∃ a ∈ Y, a ∈ bits) (hE : Sym4 E) :
    ∃ g', 1 ≤ g' ∧ mhBase.Reach
      (hd Q.BK2 ((bitsOf R).reverse ++ List.replicate g 0 ++ [0, c]) (1 :: (Y ++ E)))
      (hd Q.BK2 ((bitsOf (rot R)).reverse ++ List.replicate g' 0 ++ [0, cdn c]) (1 :: (Y ++ E))) := by
  have hYE : Sym4 (Y ++ E) := hY.sym4.app hE
  have hA := segA0 (bitsOf R).reverse (Y ++ E) g c hc (bitsOf_rev R) hYE
  have hX : Sym4 (List.replicate g 0 ++ 0 :: (cdn c :: 1 :: (Y ++ E))) :=
    (zeros4 g).app (Sym4.cons (by simp [ALL]) (Sym4.cons (cdn_all c) (Sym4.cons (by simp [ALL]) hYE)))
  obtain ⟨R', H, hrot, -, -, hr⟩ := rotate rotNormal R hR.1 _ hX
  rw [rst_hd, rnav_hd] at hr
  obtain ⟨p, b, X, rfl, hb, hX'⟩ := mb Y hY hYb
  have hB := segB R'.reverse [] (X ++ E) H.length g p (cdn c) b (cdn_cases c) hb (bits_of_eq hrot) Bits.nil
    (hX'.app hE)
  refine ⟨H.length + g + 1, by omega, (hA.ofEq rfl (hd_eq rfl ?_)).trans (hr.trans (hB.ofEq (hdR_eq rfl ?_) (hd_eq ?_ ?_)))⟩
  · simp
  · simp [rep_rep]
  · rw [hrot]
    simp [List.replicate_succ, rep_rep]
  · simp

/-- The whole count-down: `iota` rotations, leaving a blank scanned cell. -/
theorem countdown (R : List Bool) (hR : InvR R) (g : Nat) (hg : 1 ≤ g) (Y E : List Nat) (x : Option Bool)
    (hY : NoB Y) (hYb : ∃ a ∈ Y, a ∈ bits) (hE : Sym4 E) :
    ∃ g', 1 ≤ g' ∧ mhBase.Reach
      (hd Q.BK2 ((bitsOf R).reverse ++ List.replicate g 0 ++ [0, cellN x]) (1 :: (Y ++ E)))
      (hd Q.BK2 ((bitsOf (rotN (iota x) R)).reverse ++ List.replicate g' 0 ++ [0, 0]) (1 :: (Y ++ E))) := by
  rcases x with _ | _ | _
  · exact ⟨g, hg, LTM.Reach.refl _ _⟩
  · obtain ⟨g', hg', h⟩ := cdStep R hR g Y E 2 (by simp [bits]) hY hYb hE
    exact ⟨g', hg', h⟩
  · obtain ⟨g1, _, h1⟩ := cdStep R hR g Y E 3 (by simp [bits]) hY hYb hE
    obtain ⟨g2, hg2, h2⟩ := cdStep (rot R) (inv_rot hR) g1 Y E 2 (by simp [bits]) hY hYb hE
    exact ⟨g2, hg2, h1.trans h2⟩


/-! ## Fuel decrement after the count-down -/

theorem dec (ds : List Dg) (hds : Dig ds) (Qw W S : List Nat) (g : Nat) (hQ : Bits Qw) (hW : NoB W)
    (hS : Sym4 S) :
    (0 < valr ds → ∃ ds', Dig ds' ∧ ds'.map Prod.fst = ds.map Prod.fst ∧ valr ds' + 1 = valr ds ∧
      mhBase.Reach
        (hd Q.BK2 (Qw ++ List.replicate g 0 ++ [0, 0]) (1 :: 1 :: (W ++ 1 :: (FWr ds ++ 0 :: S))))
        (hd Q.FBACK (Qw ++ List.replicate g 0 ++ [0, 0]) (1 :: 1 :: (W ++ 1 :: (FWr ds' ++ 0 :: S))))) ∧
    (valr ds = 0 →
      mhBase.Reach
        (hd Q.BK2 (Qw ++ List.replicate g 0 ++ [0, 0]) (1 :: 1 :: (W ++ 1 :: (FWr ds ++ 0 :: S))))
        (hd Q.EXH (Qw ++ List.replicate g 0 ++ [0, 0]) (1 :: 1 :: (W ++ 1 :: (FWr (full ds) ++ 0 :: S))))) := by
  have hC : mhBase.Reach
      (hd Q.BK2 (Qw ++ List.replicate g 0 ++ [0, 0]) (1 :: 1 :: (W ++ 1 :: (FWr ds ++ 0 :: S))))
      (hd Q.DEC1 (Qw ++ List.replicate g 0 ++ [0, 0] ++ 1 :: 1 :: W ++ [1] ++ FWr ds) (0 :: S)) :=
    (segC0 Qw W (FWr ds) S g hQ hW (FWr_noB ds) hS).ofEq (hd_eq rfl (by simp)) (hd_eq (by simp) (by simp))
  have h1 : (1 : Nat) ∈ NB := by simp [NB]
  have hL0 : Sym4 (Qw ++ List.replicate g 0 ++ [0, 0]) :=
    (hQ.sym4.app (zeros4 g)).app (Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) Sym4.nil))
  have hW1 : NoB (1 :: 1 :: W) := NoB.cons h1 (NoB.cons h1 hW)
  have hLL : Sym4 (Qw ++ List.replicate g 0 ++ [0, 0] ++ 1 :: 1 :: W) := hL0.app hW1.sym4
  have hS0 : Sym4 (0 :: S) := Sym4.cons (by simp [ALL]) hS
  have hF := fuel ds hds _ (0 :: S) hLL hS0 (Or.inr (Or.inr ⟨S, rfl⟩))
  refine ⟨fun hpos => ?_, fun h0 => ?_⟩
  · obtain ⟨ds', hd', hm, hv, hr⟩ := hF.1 hpos
    have hwk := walkL Q.FBACK (Or.inl rfl) (Qw ++ List.replicate g 0 ++ [0, 0]) (1 :: 1 :: W ++ [1])
      (FWr ds' ++ 0 :: S) hL0 (NoB.cons h1 (NoB.cons h1 (hW.app (NoB.cons h1 NoB.nil))))
      ((FWr_noB ds').sym4.app hS0)
    have hr' : mhBase.Reach (hd Q.DEC1 (Qw ++ List.replicate g 0 ++ [0, 0] ++ 1 :: 1 :: W ++ [1] ++ FWr ds) (0 :: S))
        (hd Q.FBACK (Qw ++ List.replicate g 0 ++ [0, 0] ++ 1 :: 1 :: W ++ [1]) (FWr ds' ++ 0 :: S)) :=
      hr.ofEq (hd_eq (by simp) rfl) rfl
    exact ⟨ds', hd', hm, hv, (hC.trans (hr'.trans (hwk.ofEq (hd_eq (by simp) rfl) rfl))).ofEq rfl (hd_eq rfl (by simp))⟩
  · have hr := hF.2 h0
    have hwk := walkL Q.EXH (Or.inr rfl) (Qw ++ List.replicate g 0 ++ [0, 0]) (1 :: 1 :: W)
      (1 :: (FWr (full ds) ++ 0 :: S)) hL0 hW1 (Sym4.cons (by simp [ALL]) ((FWr_noB _).sym4.app hS0))
    have hr' : mhBase.Reach (hd Q.DEC1 (Qw ++ List.replicate g 0 ++ [0, 0] ++ 1 :: 1 :: W ++ [1] ++ FWr ds) (0 :: S))
        (hd Q.EXH (Qw ++ List.replicate g 0 ++ [0, 0] ++ 1 :: 1 :: W) (1 :: (FWr (full ds) ++ 0 :: S))) :=
      hr.ofEq (hd_eq (by simp) rfl) rfl
    exact (hC.trans (hr'.trans (hwk.ofEq (hd_eq (by simp) rfl) rfl))).ofEq rfl (hd_eq rfl (by simp))

/-! ## After a move: record rotation and the jump tokens -/

theorem post (R1 : List Bool) (h0 : false ∈ R1) (Lw2 : List Nat) (ch2 p b : Nat) (X2 : List Nat) (y : Nat)
    (hL : Bits Lw2) (hch : ch2 = 0 ∨ ch2 = 2 ∨ ch2 = 3) (hb : b ∈ bits) (hX2 : Sym4 X2) :
    ∃ g', 1 ≤ g' ∧ mhBase.Reach
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



/-! ## Configurations -/

theorem bitsOf_cons (b : Bool) (l : List Bool) : bitsOf (b :: l) = bn b :: bitsOf l := rfl

theorem bits3 (a b c : Bool) (rest : List Bool) :
    (bitsOf (a :: b :: c :: rest)).reverse = (bitsOf rest).reverse ++ [bn c, bn b, bn a] := by
  simp [bitsOf, bn]

theorem bits1 (a : Bool) (rest : List Bool) :
    (bitsOf (a :: rest)).reverse = (bitsOf rest).reverse ++ [bn a] := by
  simp [bitsOf, bn]

/-- The step boundary: `BK2` on the scanned cell `c`; `Y` is `M_g W M_3 F` (no blank), `E` the rest
(the blank after the fuel and the storage). -/
def Bd (R : List Bool) (g : Nat) (c : Option Bool) (Y E : List Nat) : ZC :=
  hd Q.BK2 ((bitsOf R).reverse ++ List.replicate g 0 ++ [0, cellN c]) (1 :: (Y ++ E))

/-- The result state: the outcome `o` is written, everything left of `M_g` is erased. -/
def RE (o : Bool) (V : List Nat) : ZC := hdR (dpOf (bn o)) [1] V

/-- The one machine-specific step of the act: from `GH w d` on `H` to `G2 w d` right of it. -/
def GHStep (L : LTM) : Prop :=
  ∀ (w d : Bool) (A V : List Nat), Sym4 A → Sym4 V → L.Reach (hdR (ghOf (bn w) (bn d)) A (1 :: V)) (hdR (g2Of w d) (A ++ [1]) V)

/-! ## The peek: halt, or the act and the record rotation -/

theorem peek (L : LTM) (hext : mhBase.Ext L) (hGH : GHStep L) (R1 : List Bool) (hR1 : InvR R1) (g : Nat)
    (x : List Bool) (pos : List Nat) (cur : Nat) (hcur : cur < pos.length)
    (hpos : ∀ p ∈ pos, p ≤ x.length + 1) (Y0 : List Nat) (hY0 : NoB Y0) (hYb : ∃ a ∈ Y0, a ∈ bits) :
    (R1.getD 2 false = false → L.Reach
      (hd Q.FBACK ((bitsOf R1).reverse ++ List.replicate g 0 ++ [0, 0]) (1 :: 1 :: (Y0 ++ 0 :: storeOf x pos cur)))
      (RE (R1.getD 0 false) (Y0 ++ 0 :: storeOf x pos cur))) ∧
    (R1.getD 2 false = true → ∃ g', 1 ≤ g' ∧ L.Reach
      (hd Q.FBACK ((bitsOf R1).reverse ++ List.replicate g 0 ++ [0, 0]) (1 :: 1 :: (Y0 ++ 0 :: storeOf x pos cur)))
      (Bd (rotN (entryOnes R1 + 1) (rot R1)) g'
        (mhRead x ((actPos x.length (R1.getD 0 false) (R1.getD 1 false) pos cur).getD
          (actCur (pos.length - 1) (R1.getD 0 false) (R1.getD 1 false) cur) 0))
        (1 :: Y0)
        (0 :: storeOf x (actPos x.length (R1.getD 0 false) (R1.getD 1 false) pos cur)
          (actCur (pos.length - 1) (R1.getD 0 false) (R1.getD 1 false) cur)))) := by
  have hS := sym4_storeOf x pos cur
  have h1 : (1 : Nat) ∈ NB := by simp [NB]
  have hV : Sym4 (Y0 ++ 0 :: storeOf x pos cur) := hY0.sym4.app (Sym4.cons (by simp [ALL]) hS)
  rcases R1 with _ | ⟨r0, _ | ⟨r1, _ | ⟨r2, rest⟩⟩⟩
  · exact absurd hR1.1 (by simp)
  · have e := hR1.2.1 rfl
    simp only [List.cons.injEq, and_true] at e
    subst e
    refine ⟨fun _ => ?_, fun h => by simp at h⟩
    exact hext.reach ((segShort1 _ g hV).ofEq (hd_eq (by simp [bitsOf, bn]) rfl) rfl)
  · have e := hR1.2.2 rfl
    simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] at e
    subst e
    refine ⟨fun _ => ?_, fun h => by simp at h⟩
    have h := segShort2 (Y0 ++ 0 :: storeOf x pos cur) g (bn r0) (bn_bits r0) hV
    exact hext.reach (h.ofEq (hd_eq (by cases r0 <;> simp [bitsOf, bn]) rfl) (by cases r0 <;> rfl))
  · have hrest : Bits (bitsOf rest).reverse := bitsOf_rev rest
    have hf : false ∈ r0 :: r1 :: r2 :: rest := hR1.1
    refine ⟨fun h2 => ?_, fun h2 => ?_⟩
    · have h2' : r2 = false := h2
      subst h2'
      have h := segHalt (bitsOf rest).reverse (Y0 ++ 0 :: storeOf x pos cur) g (bn r0) (bn r1) (bn_bits r0)
        (bn_bits r1) hrest hV
      exact hext.reach (h.ofEq (hd_eq (by rw [bits3]; rfl) rfl) (by cases r0 <;> rfl))
    · have h2' : r2 = true := h2
      subst h2'
      have hcode : (bitsOf (r0 :: r1 :: true :: rest)).reverse = (bitsOf rest).reverse ++ [3, bn r1, bn r0] := by
        rw [bits3]; rfl
      have hY : NoB (1 :: Y0) := NoB.cons h1 hY0
      have hYb' : ∃ a ∈ 1 :: Y0, a ∈ bits :=
        let ⟨a, ha, hab⟩ := hYb; ⟨a, List.mem_cons_of_mem _ ha, hab⟩
      obtain ⟨p, b, X, eY, hb, hX⟩ := mb (1 :: Y0) hY hYb'
      cases p with
      | zero =>
        simp only [List.replicate_zero, List.nil_append, List.cons.injEq] at eY
        have := eY.1
        rcases mem_bits hb with rfl | rfl <;> simp at this
      | succ p' =>
        have hY0e : Y0 = List.replicate p' 1 ++ b :: X := by
          simpa [List.replicate_succ] using eY
        subst hY0e
        have e0 : (r0 :: r1 :: true :: rest).getD 0 false = r0 := rfl
        have e1 : (r0 :: r1 :: true :: rest).getD 1 false = r1 := rfl
        rw [e0, e1]
        have hQc : Bits ((bitsOf rest).reverse ++ [3, bn r1, bn r0]) :=
          hrest.app (Bits.cons (by simp [bits]) (Bits.cons (bn_bits r1) (Bits.cons (bn_bits r0) Bits.nil)))
        -- the peek reads (w, d) and enters `G2 w d`
        have hPk := segPk (bitsOf rest).reverse (1 :: (List.replicate p' 1 ++ b :: X ++ 0 :: storeOf x pos cur)) g
          (bn r0) (bn r1) (bn_bits r0) (bn_bits r1) hrest (Sym4.cons (by simp [ALL]) hV)
        have hS0 := sym4_storeOf x pos cur
        have hG := hGH r0 r1 ((bitsOf rest).reverse ++ [3, bn r1, bn r0] ++ List.replicate g 0 ++ [0, 0])
          (1 :: (List.replicate p' 1 ++ b :: X ++ 0 :: storeOf x pos cur))
          (by have h1u : (1 : Nat) ∈ ALL := by simp [ALL]
              have h0u : (0 : Nat) ∈ ALL := by simp [ALL]
              have h3u : (3 : Nat) ∈ ALL := by simp [ALL]
              have hb' : ∀ c, c ∈ bits → c ∈ ALL := fun c hc => by
                rcases mem_bits hc with rfl | rfl <;> simp [ALL]
              have hrep : ∀ (k c : Nat), c ∈ ALL → Sym4 (List.replicate k c) := fun k c hc a ha => by
                rw [List.eq_of_mem_replicate ha]; exact hc
              simp only [List.append_assoc, List.cons_append, List.nil_append]
              exact hrest.sym4.app (Sym4.cons h3u (Sym4.cons (hb' _ (bn_bits r1)) (Sym4.cons (hb' _ (bn_bits r0))
                ((hrep _ _ h0u).app (Sym4.cons h0u (Sym4.cons h0u Sym4.nil)))))))
          (by have h1u : (1 : Nat) ∈ ALL := by simp [ALL]
              have h0u : (0 : Nat) ∈ ALL := by simp [ALL]
              have hb' : ∀ c, c ∈ bits → c ∈ ALL := fun c hc => by
                rcases mem_bits hc with rfl | rfl <;> simp [ALL]
              have hrep : ∀ (k c : Nat), c ∈ ALL → Sym4 (List.replicate k c) := fun k c hc a ha => by
                rw [List.eq_of_mem_replicate ha]; exact hc
              simp only [List.append_assoc, List.cons_append, List.nil_append]
              exact Sym4.cons h1u ((hrep _ _ h1u).app (Sym4.cons (hb' _ hb) (hX.app (Sym4.cons h0u hS0)))))
        have hAct := act r0 r1 x pos cur hcur hpos ((bitsOf rest).reverse ++ [3, bn r1, bn r0]) (1 :: (List.replicate p' 1 ++ b :: X))
          g hQc hY
        generalize actPos x.length r0 r1 pos cur = pos' at hAct ⊢
        generalize actCur (pos.length - 1) r0 r1 cur = cur' at hAct ⊢
        have hS' := sym4_storeOf x pos' cur'
        have hpost := post (r0 :: r1 :: true :: rest) hf [] (cellN (mhRead x (pos'.getD cur' 0))) (p' + 1) b
          (X ++ 0 :: storeOf x pos' cur') g Bits.nil (cellN_cases _) hb
          (hX.app (Sym4.cons (by simp [ALL]) hS'))
        obtain ⟨g', hg', hp⟩ := hpost
        refine ⟨g', hg', ?_⟩
        unfold Bd
        have s1 : L.Reach
            (hd Q.FBACK ((bitsOf (r0 :: r1 :: true :: rest)).reverse ++ List.replicate g 0 ++ [0, 0])
              (1 :: 1 :: (List.replicate p' 1 ++ b :: X ++ 0 :: storeOf x pos cur)))
            (hdR (ghOf (bn r0) (bn r1)) ((bitsOf rest).reverse ++ [3, bn r1, bn r0] ++ List.replicate g 0 ++ [0, 0])
              (1 :: 1 :: (List.replicate p' 1 ++ b :: X ++ 0 :: storeOf x pos cur))) :=
          (hext.reach hPk).ofEq (hd_eq (by rw [hcode]) (by simp)) (hdR_eq rfl (by simp))
        have s3 : L.Reach
            (hdR (g2Of r0 r1) ((bitsOf rest).reverse ++ [3, bn r1, bn r0] ++ List.replicate g 0 ++ [0, 0] ++ [1])
              (1 :: (List.replicate p' 1 ++ b :: X ++ 0 :: storeOf x pos cur)))
            (hd Q.RTW ((bitsOf rest).reverse ++ [3, bn r1, bn r0]) (List.replicate g 0 ++ 0 ::
              cellN (mhRead x (pos'.getD cur' 0)) :: 1 ::
              (1 :: (List.replicate p' 1 ++ b :: X) ++ 0 :: storeOf x pos' cur'))) :=
          (hext.reach hAct).ofEq (hdR_eq (by simp) (by simp)) rfl
        have s4 : L.Reach
            (hd Q.RTW ((bitsOf rest).reverse ++ [3, bn r1, bn r0]) (List.replicate g 0 ++ 0 ::
              cellN (mhRead x (pos'.getD cur' 0)) :: 1 ::
              (1 :: (List.replicate p' 1 ++ b :: X) ++ 0 :: storeOf x pos' cur')))
            (hd Q.BK2 ((bitsOf (rotN (entryOnes (r0 :: r1 :: true :: rest) + 1) (rot (r0 :: r1 :: true :: rest)))).reverse ++
              List.replicate g' 0 ++ [0, cellN (mhRead x (pos'.getD cur' 0))])
              (1 :: (1 :: (List.replicate p' 1 ++ b :: X) ++ 0 :: storeOf x pos' cur'))) :=
          (hext.reach hp).ofEq (hd_eq (by rw [hcode]) (by simp [List.replicate_succ])) (hd_eq rfl (by simp [List.replicate_succ]))
        exact s1.trans ((hG.ofEq rfl rfl).trans (s3.trans s4))


/-! ## The whole run -/

theorem runMHAux_succ (np : Nat) (x : List Bool) (T : Nat) (R0 : List Bool) (pos : List Nat) (c : Nat) :
    runMHAux np x (T + 1) R0 pos c =
      (if (rotN (iota (mhRead x (pos.getD c 0))) R0).getD 2 false then
        runMHAux np x T (rotN (entryOnes (rotN (iota (mhRead x (pos.getD c 0))) R0) + 1)
          (rot (rotN (iota (mhRead x (pos.getD c 0))) R0)))
          (actPos x.length ((rotN (iota (mhRead x (pos.getD c 0))) R0).getD 0 false)
            ((rotN (iota (mhRead x (pos.getD c 0))) R0).getD 1 false) pos c)
          (actCur np ((rotN (iota (mhRead x (pos.getD c 0))) R0).getD 0 false)
            ((rotN (iota (mhRead x (pos.getD c 0))) R0).getD 1 false) c)
      else (rotN (iota (mhRead x (pos.getD c 0))) R0).getD 0 false) := by
  simp only [runMHAux]
  generalize rotN (iota (mhRead x (pos.getD c 0))) R0 = R
  by_cases h2 : R.getD 2 false = true
  · simp only [h2, ite_true]
    cases h0 : R.getD 0 false <;> cases h1 : R.getD 1 false <;> simp [h0, h1, actPos, actCur]
  · have h2' : R.getD 2 false = false := by simpa using h2
    simp only [h2', Bool.false_eq_true, ite_false]

theorem actPos_len (n : Nat) (w d : Bool) (pos : List Nat) (cur : Nat) :
    (actPos n w d pos cur).length = pos.length := by
  cases w <;> simp [actPos]

theorem actCur_lt (np : Nat) (w d : Bool) (cur : Nat) (h : cur < np + 1) : actCur np w d cur < np + 1 := by
  unfold actCur
  split <;> (try split) <;> omega

theorem runMHI (L : LTM) (hext : mhBase.Ext L) (hGH : GHStep L) (x : List Bool) (W : List Nat) (hW : NoB W)
    (np : Nat) :
    ∀ (T : Nat) (R : List Bool) (g : Nat) (pos : List Nat) (cur : Nat) (ds : List Dg),
      InvR R → 1 ≤ g → pos.length = np + 1 → cur < pos.length → (∀ p ∈ pos, p ≤ x.length + 1) →
      Dig ds → ds ≠ [] → valr ds = T →
      ∃ ds' pos' cur', Dig ds' ∧ ds'.map Prod.fst = ds.map Prod.fst ∧ pos'.length = np + 1 ∧
        cur' < pos'.length ∧ (∀ p ∈ pos', p ≤ x.length + 1) ∧
        L.Reach (Bd R g (mhRead x (pos.getD cur 0)) (1 :: (W ++ 1 :: FWr ds)) (0 :: storeOf x pos cur))
          (RE (runMHAux np x T R pos cur) (W ++ 1 :: (FWr ds' ++ 0 :: storeOf x pos' cur')))
  | T, R, g, pos, cur, ds, hR, hg, hnp, hcur, hpos, hds, hne, hv => by
    have h1 : (1 : Nat) ∈ NB := by simp [NB]
    have hS := sym4_storeOf x pos cur
    have hY0 : NoB (W ++ 1 :: FWr ds) := hW.app (NoB.cons h1 (FWr_noB ds))
    have hY : NoB (1 :: (W ++ 1 :: FWr ds)) := NoB.cons h1 hY0
    have hYb : ∃ a ∈ 1 :: (W ++ 1 :: FWr ds), a ∈ bits := by
      obtain ⟨a, ha, hab⟩ := fw_bit ds hne
      exact ⟨a, List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ ha)), hab⟩
    have hE : Sym4 (0 :: storeOf x pos cur) := Sym4.cons (by simp [ALL]) hS
    obtain ⟨g1, hg1, hcd⟩ := countdown R hR g hg (1 :: (W ++ 1 :: FWr ds)) (0 :: storeOf x pos cur)
      (mhRead x (pos.getD cur 0)) hY hYb hE
    have hR1 : InvR (rotN (iota (mhRead x (pos.getD cur 0))) R) := inv_rotN hR _
    have hD := dec ds hds (bitsOf (rotN (iota (mhRead x (pos.getD cur 0))) R)).reverse W (storeOf x pos cur) g1
      (bitsOf_rev _) hW hS
    generalize eR : rotN (iota (mhRead x (pos.getD cur 0))) R = R1 at hcd hR1 hD
    have hstart : mhBase.Reach (Bd R g (mhRead x (pos.getD cur 0)) (1 :: (W ++ 1 :: FWr ds)) (0 :: storeOf x pos cur))
        (hd Q.BK2 ((bitsOf R1).reverse ++ List.replicate g1 0 ++ [0, 0])
          (1 :: 1 :: (W ++ 1 :: (FWr ds ++ 0 :: storeOf x pos cur)))) :=
      hcd.ofEq rfl (hd_eq rfl (by simp))
    cases T with
    | zero =>
      refine ⟨full ds, pos, cur, ?_, by simp [full], hnp, hcur, hpos, ?_⟩
      · intro q hq
        obtain ⟨_, -, rfl⟩ := List.mem_map.mp hq
        exact Nat.le_refl _
      · have hE0 := hD.2 hv
        obtain ⟨r, rest, e⟩ : ∃ r rest, R1 = r :: rest := by
          cases h : R1 with
          | nil => rw [h] at hR1; exact absurd hR1.1 (by simp)
          | cons r rest => exact ⟨r, rest, rfl⟩
        subst e
        have hx := segExh0 (bitsOf rest).reverse (W ++ 1 :: (FWr (full ds) ++ 0 :: storeOf x pos cur)) g1 (bn r)
          (bn_bits r) (bitsOf_rev _)
          (hW.sym4.app (Sym4.cons (by simp [ALL]) (((FWr_noB _).sym4).app (Sym4.cons (by simp [ALL]) hS))))
        have hx' : mhBase.Reach (hd Q.EXH ((bitsOf (r :: rest)).reverse ++ List.replicate g1 0 ++ [0, 0])
            (1 :: 1 :: (W ++ 1 :: (FWr (full ds) ++ 0 :: storeOf x pos cur))))
            (hdR Q.DP10 [1] (W ++ 1 :: (FWr (full ds) ++ 0 :: storeOf x pos cur))) :=
          hx.ofEq (hd_eq (by simp [bits1]) (by simp)) rfl
        have hfin := (hstart.trans (hE0.trans hx'))
        exact (hext.reach hfin).ofEq rfl (by simp [RE, dpOf, bn, runMHAux])
    | succ T =>
      have hpos0 : 0 < valr ds := by omega
      obtain ⟨ds1, hd1, hm1, hv1, hdec⟩ := hD.1 hpos0
      have hne1 : ds1 ≠ [] := by
        intro h
        apply hne
        rw [h] at hm1
        simpa using hm1.symm
      have hY1 : NoB (W ++ 1 :: FWr ds1) := hW.app (NoB.cons h1 (FWr_noB ds1))
      have hYb1 : ∃ a ∈ W ++ 1 :: FWr ds1, a ∈ bits := by
        obtain ⟨a, ha, hab⟩ := fw_bit ds1 hne1
        exact ⟨a, List.mem_append_right _ (List.mem_cons_of_mem _ ha), hab⟩
      have hpk := peek L hext hGH R1 hR1 g1 x pos cur hcur hpos _ hY1 hYb1
      have hst : L.Reach (Bd R g (mhRead x (pos.getD cur 0)) (1 :: (W ++ 1 :: FWr ds)) (0 :: storeOf x pos cur))
          (hd Q.FBACK ((bitsOf R1).reverse ++ List.replicate g1 0 ++ [0, 0])
            (1 :: 1 :: ((W ++ 1 :: FWr ds1) ++ 0 :: storeOf x pos cur))) :=
        (hext.reach (hstart.trans hdec)).ofEq rfl (hd_eq rfl (by simp))
      rw [runMHAux_succ, eR]
      by_cases h2 : R1.getD 2 false = true
      · obtain ⟨g', hg', hpk2⟩ := hpk.2 h2
        have hl : pos.length - 1 = np := by omega
        rw [hl] at hpk2
        simp only [h2, ite_true]
        obtain ⟨ds', pos', cur', hd', hm', hl', hc', hb', hr⟩ := runMHI L hext hGH x W hW np T
          (rotN (entryOnes R1 + 1) (rot R1)) g'
          (actPos x.length (R1.getD 0 false) (R1.getD 1 false) pos cur)
          (actCur np (R1.getD 0 false) (R1.getD 1 false) cur) ds1
          (inv_rotN (inv_rot hR1) _) hg' (by rw [actPos_len]; exact hnp)
          (by rw [actPos_len, hnp]; exact actCur_lt np _ _ _ (by omega))
          (actPos_bound _ _ _ _ _ hpos) hd1 hne1 (by omega)
        exact ⟨ds', pos', cur', hd', hm'.trans hm1, hl', hc', hb', (hst.trans hpk2).trans hr⟩
      · have h2' : R1.getD 2 false = false := by simpa using h2
        have hk := hpk.1 h2'
        simp only [h2', Bool.false_eq_true, ite_false]
        exact ⟨ds1, pos, cur, hd1, hm1, hnp, hcur, hpos, (hst.trans hk).ofEq rfl (hdR_eq rfl (by simp))⟩
termination_by T _ _ _ _ _ _ _ _ _ _ _ _ _ => T

end ZP.MH
