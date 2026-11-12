module

public import ZP.MHRun
public import ZP.ExtChecksMH

@[expose] public section

/-!
# Multihead run for `Z_LNL`: the two-step peek

`ZP/MHRun.lean` assumes that the peek `GH w d` on `H` reaches `G2 w d` right of `H` in one step. In `zlnl` the
peek first looks at the cell right of `H` (`XW w d`): during a decider run it is `M_g`, which sends the head on
to `G2 w d` right of `M_g`. This file restates `peek` and `runMHI` for that two-step version (`GHStepL`); the
proofs are those of `ZP/MHRun.lean`, with the act entered one cell later (`tailG2` absorbs the extra step of `G2`).
-/

namespace ZP.MH

open ZP

/-- The peek of `zlnl`: `GH w d` on `H`, `XW w d` on `M_g`, then `G2 w d` right of `M_g`. -/
def GHStepL (L : LTM) : Prop :=
  ∀ (w d : Bool) (A V : List Nat), Sym4 A → Sym4 V →
    L.Reach (hdR (ghOf (bn w) (bn d)) A (1 :: 1 :: V)) (hdR (g2Of w d) (A ++ [1, 1]) V)

theorem ghStepL_zlnl : GHStepL zlnlLogic := by
  intro w d A V hA hV
  have hv : Valid [ALL, ALL] [A, V] := Valid.cons hA (Valid.cons hV (Valid.nil _))
  cases w <;> cases d <;>
  exact checkFF (env := [A, V]) (E := []) (k := 2) hv trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .sym 1, .blk 1 .id])
    (ls' := [.blk 0 .id, .sym 1, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by simp [dR, Item.den, List.getD, map_id_app]) (by simp [dR, Item.den, List.getD, map_id_app])
    (by simp [dR, Item.den, List.getD, map_id_app]) (by simp [dR, Item.den, List.getD, map_id_app])

theorem hdR_q (q : Nat) (A R : List Nat) : (hdR q A R).q = q := rfl

theorem zstep_tail {L : LTM} {c c' X : ZC} (hs : L.zstep c = some c') (hr : L.Reach c X) (hne : c.q ≠ X.q) :
    L.Reach c' X := by
  obtain ⟨n, hn⟩ := hr
  cases n with
  | zero =>
    cases hn
    exact absurd rfl hne
  | succ n =>
    refine ⟨n, ?_⟩
    have h : (if c.q = L.beep then none else (L.zstep c).bind (L.zrun n)) = some X := hn
    by_cases hb : c.q = L.beep
    · rw [ite_eq_left hb] at h; cases h
    · rw [ite_eq_right hb, hs] at h
      exact h

theorem g2_step (w d : Bool) (A V : List Nat) :
    mhBase.zstep (hdR (g2Of w d) A (1 :: V)) = some (hdR (g2Of w d) (A ++ [1]) V) := by
  have e1 : (⟨g2Of w d, [Item.blk 0 .id].reverse, [.sym 1, .blk 1 .id], false⟩ : SC).den [A, V] =
      hdR (g2Of w d) A (1 :: V) := den_tapeR (by simp [dR, Item.den, List.getD, map_id_app])
        (by simp [dR, Item.den, List.getD, map_id_app])
  have e2 : (⟨g2Of w d, [Item.blk 0 .id, .sym 1].reverse, [.blk 1 .id], false⟩ : SC).den [A, V] =
      hdR (g2Of w d) (A ++ [1]) V := den_tapeR (by simp [dR, Item.den, List.getD, map_id_app])
        (by simp [dR, Item.den, List.getD, map_id_app])
  rw [← e1, ← e2]
  cases w <;> cases d <;> exact cstep_zstep (by decide +kernel)

theorem tailG2 {L : LTM} (hext : mhBase.Ext L) (w d : Bool) (A V : List Nat) {X : ZC}
    (h : L.Reach (hdR (g2Of w d) A (1 :: V)) X) (hq : X.q = Q.RTW) :
    L.Reach (hdR (g2Of w d) (A ++ [1]) V) X := by
  refine zstep_tail (hext.zstep (g2_step w d A V)) h ?_
  rw [hq, hdR_q]
  cases w <;> cases d <;> decide

theorem peekL (L : LTM) (hext : mhBase.Ext L) (hGH : GHStepL L) (R1 : List Bool) (hR1 : InvR R1) (g : Nat)
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
        have hG := hGH r0 r1 ((bitsOf rest).reverse ++ [3, bn r1, bn r0] ++ List.replicate g 0 ++ [0, 0])
          (List.replicate p' 1 ++ b :: X ++ 0 :: storeOf x pos cur)
          (((hQc.sym4).app (zeros4 g)).app (Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) Sym4.nil)))
          (((ones4 p').app (Sym4.cons (by rcases mem_bits hb with rfl | rfl <;> simp [ALL]) hX)).app
            (Sym4.cons (by simp [ALL]) hS))
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
            (hdR (g2Of r0 r1) ((bitsOf rest).reverse ++ [3, bn r1, bn r0] ++ List.replicate g 0 ++ [0, 0] ++ [1, 1])
              (List.replicate p' 1 ++ b :: X ++ 0 :: storeOf x pos cur))
            (hd Q.RTW ((bitsOf rest).reverse ++ [3, bn r1, bn r0]) (List.replicate g 0 ++ 0 ::
              cellN (mhRead x (pos'.getD cur' 0)) :: 1 ::
              (1 :: (List.replicate p' 1 ++ b :: X) ++ 0 :: storeOf x pos' cur'))) := by
          have := tailG2 hext r0 r1 ((bitsOf rest).reverse ++ [3, bn r1, bn r0] ++ List.replicate g 0 ++ [0, 0] ++ [1])
            (List.replicate p' 1 ++ b :: X ++ 0 :: storeOf x pos cur) (hext.reach hAct |>.ofEq (hdR_eq (by simp) (by simp)) rfl) rfl
          exact this.ofEq (hdR_eq (by simp) rfl) rfl
        have s4 : L.Reach
            (hd Q.RTW ((bitsOf rest).reverse ++ [3, bn r1, bn r0]) (List.replicate g 0 ++ 0 ::
              cellN (mhRead x (pos'.getD cur' 0)) :: 1 ::
              (1 :: (List.replicate p' 1 ++ b :: X) ++ 0 :: storeOf x pos' cur')))
            (hd Q.BK2 ((bitsOf (rotN (entryOnes (r0 :: r1 :: true :: rest) + 1) (rot (r0 :: r1 :: true :: rest)))).reverse ++
              List.replicate g' 0 ++ [0, cellN (mhRead x (pos'.getD cur' 0))])
              (1 :: (1 :: (List.replicate p' 1 ++ b :: X) ++ 0 :: storeOf x pos' cur'))) :=
          (hext.reach hp).ofEq (hd_eq (by rw [hcode]) (by simp [List.replicate_succ])) (hd_eq rfl (by simp [List.replicate_succ]))
        exact s1.trans ((hG.ofEq rfl (hdR_eq (by simp) rfl)).trans (s3.trans s4))


/-! ## The whole run -/

theorem runMHIL (L : LTM) (hext : mhBase.Ext L) (hGH : GHStepL L) (x : List Bool) (W : List Nat) (hW : NoB W)
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
      have hpk := peekL L hext hGH R1 hR1 g1 x pos cur hcur hpos _ hY1 hYb1
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
        obtain ⟨ds', pos', cur', hd', hm', hl', hc', hb', hr⟩ := runMHIL L hext hGH x W hW np T
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
