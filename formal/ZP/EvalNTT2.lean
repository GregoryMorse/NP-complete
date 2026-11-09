module

public import ZP.EvalNTT

@[expose] public section

/-! # NTT machine: the evaluation phase (part 2): odometer bridge and refutation -/

namespace ZP.NTT

open ZP ZP.G

/-! ## Bridge: odometer records to cursor records -/

/-- The record of an odometer assignment right after witness initialisation, with input flag `x`. -/
def ORec.toRc (o : ORec) (x : Nat) : Rc :=
  { F := o.F, O := o.O, Pf := x, acc := o.acc, E := 3 :: 3 :: List.replicate (o.E.length - 2) 2,
    b0 := (therm o.d o.r).headD 2, br := (therm o.d o.r).tail,
    u0 := (winStr o.z o.k o.m).headD 2, ur := (winStr o.z o.k o.m).tail }

/-- The same record in cursor form at the start of a pass. -/
def ORec.vr (o : ORec) (x : Nat) : VR :=
  { F := 2, O := o.O, P := x, w := o.acc.length, k := if x = 3 then 2 else 1,
    E := 3 :: 3 :: List.replicate (o.E.length - 2) 2, m := 0, n := o.d, s := o.r - (o.d + 1),
    a := 0, c := o.z + o.k - 1, t := o.m }

theorem restoreU_win (z k m : Nat) (hk : 1 ≤ k) :
    restoreU (winStr z k m) = List.replicate (z + k) 3 ++ List.replicate m 2 := by
  obtain ⟨o, rfl⟩ : ∃ o, k = o + 1 := ⟨k - 1, by omega⟩
  have h := restoreU_rep z (List.replicate o 3 ++ List.replicate m 2)
  have e1 : winStr z (o + 1) m = List.replicate z 2 ++ 3 :: (List.replicate o 3 ++ List.replicate m 2) := by
    simp [winStr, List.replicate_succ]
  rw [e1, h]
  have : List.replicate (z + (o + 1)) 3 = List.replicate z 3 ++ 3 :: List.replicate o 3 := by
    rw [← List.replicate_append_replicate]; simp [List.replicate_succ]
  rw [this]; simp


theorem toRc_rest (o : ORec) (x : Nat) (hk : 1 ≤ o.k) : (o.toRc x).Rest := by
  obtain ⟨j, hj⟩ : ∃ j, o.k = j + 1 := ⟨o.k - 1, by omega⟩
  refine ⟨o.z, List.replicate j 3 ++ List.replicate o.m 2, ?_⟩
  have : (o.toRc x).u0 :: (o.toRc x).ur = winStr o.z o.k o.m := by
    simp only [ORec.toRc]
    cases h : winStr o.z o.k o.m with
    | nil => simp [winStr, hj, List.replicate_succ] at h
    | cons a l => simp
  rw [this, hj]
  simp [winStr, List.replicate_succ]

theorem accI_fld (x L : Nat) (hx : x ∈ [2, 3]) (hL : 2 ≤ L) :
    accI x L = fld L (if x = 3 then 2 else 1) := by
  simp at hx
  rcases hx with rfl | rfl
  · obtain ⟨j, rfl⟩ : ∃ j, L = j + 1 := ⟨L - 1, by omega⟩
    simp [accI, fld]
  · obtain ⟨j, rfl⟩ : ∃ j, L = j + 2 := ⟨L - 2, by omega⟩
    simp [accI, fld, List.replicate_succ]

theorem toRc_ps_vr (o : ORec) (x : Nat) (hk : 1 ≤ o.k) (hacc : 2 ≤ o.acc.length) (hx : x ∈ [2, 3]) (hd : o.d + 1 ≤ o.r) :
    1 :: 1 :: (o.toRc x).ps.body = (o.vr x).recd := by
  rw [Rc.ps_body _ (toRc_rest o x hk)]
  have hb : (o.toRc x).b0 :: (o.toRc x).br = therm o.d o.r := by
    simp only [ORec.toRc]
    cases h : therm o.d o.r with
    | nil => simp [therm] at h
    | cons a l => simp
  have hu : (o.toRc x).u0 :: (o.toRc x).ur = winStr o.z o.k o.m := by
    simp only [ORec.toRc]
    cases h : winStr o.z o.k o.m with
    | nil => obtain ⟨j, hj⟩ : ∃ j, o.k = j + 1 := ⟨o.k - 1, by omega⟩; simp [winStr, hj, List.replicate_succ] at h
    | cons a l => simp
  have e1 : (o.toRc x).b0 :: ((o.toRc x).br ++ 1 :: restoreU ((o.toRc x).u0 :: (o.toRc x).ur)) =
      therm o.d o.r ++ 1 :: (List.replicate (o.z + o.k) 3 ++ List.replicate o.m 2) := by
    rw [hu, restoreU_win _ _ _ hk]
    have : (o.toRc x).b0 :: ((o.toRc x).br ++ 1 :: (List.replicate (o.z + o.k) 3 ++ List.replicate o.m 2)) =
        ((o.toRc x).b0 :: (o.toRc x).br) ++ 1 :: (List.replicate (o.z + o.k) 3 ++ List.replicate o.m 2) := by simp
    rw [this, hb]
  obtain ⟨j, hj⟩ : ∃ j, o.k = j + 1 := ⟨o.k - 1, by omega⟩
  have hu2 : o.z + o.k - 1 + 1 = o.z + o.k := by omega
  simp only [VR.recd, VR.tl, VR.b, VR.u, ORec.vr, ORec.toRc] at e1 ⊢
  simp only [List.cons_append, List.nil_append, List.replicate_zero, hu2]
  rw [accI_fld x _ hx hacc]
  rw [e1]
  simp [therm]


def BrOk (p : ORec × Nat) : Prop := 1 ≤ p.1.k ∧ 2 ≤ p.1.acc.length ∧ p.2 ∈ [2, 3] ∧ p.1.d + 1 ≤ p.1.r

theorem tailP_vr : ∀ l : List (ORec × Nat), (∀ p ∈ l, BrOk p) →
    tailP (l.map fun p => p.1.toRc p.2) = tailVR (l.map fun p => p.1.vr p.2)
  | [], _ => by simp [tailP, tailVR]
  | p :: l, h => by
    have hp := h p (by simp)
    have := toRc_ps_vr p.1 p.2 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
    have ih := tailP_vr l (fun q hq => h q (by simp [hq]))
    simp only [List.map_cons, tailP, tailVR, List.flatten_cons]
    simp only [tailVR] at ih
    rw [ih, ← this]
    rfl


/-- The first record as cursor, in `VR` form: `FAL` .. `RFL`. -/
theorem faG (L Pm : List Nat) (hL : NoB L) (hP : GoodW Pm) (w : VR) (hw : w.Ok) (ws : List VR)
    (hws : ∀ x ∈ ws, x.Ok) (hcmp : w.O = 3 → ∃ z, 1 ≤ w.k ∧ w.E = fld (w.k + z) w.k)
    (hLe : L = Pm ++ 1 :: 1 :: ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws))) :
    znttLogic.Reach (hd QNTT.FAL L [])
      (hd QNTT.RFL (Pm ++ [1, 1] ++ [3, w.O, w.P] ++ 1 :: (w.curG.tl ++ tailVR (ws.map VR.dec))) []) := by
  have sPm := hP.sym4
  have sMM : Sym4 (Pm ++ [1, 1]) := sPm.app (sym4_M (sym4_M Sym4.nil))
  have sB : Sym4 ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws)) :=
    hw.hdr3.sym4.app (sym4_M (hw.tl_sym4.app (tailVR_sym4 ws hws)))
  have h1 := falScan L [] hL Sym4.nil
  rw [hLe] at h1
  have h2 := fasGood hP [] (1 :: 1 :: ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws))) Sym4.nil (sym4_M (sym4_M sB))
  have h3 := fasMM Pm ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws)) sPm sB
  have h4 := fa0G (Pm ++ [1, 1]) w hw ws hws sMM hcmp
  simp only [List.append_nil, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 h4 ⊢
  rw [hLe]
  simp only [List.append_nil, List.append_assoc, List.cons_append, List.nil_append]
  exact h1.trans (h2.trans (h3.trans h4))


theorem curTapeG_tl (Pm : List Nat) (pre : List Rc) (c : VR) (hk : 1 ≤ c.k) (hkw : c.k ≤ c.w) (hF : c.F = 3)
    (vs : List VR) :
    curTapeG Pm pre c 0 (c.k - 1) (c.w - c.k) vs = Pm ++ tailB pre ++ [1, 1, 3, c.O, c.P] ++ 1 :: (c.tl ++ tailVR vs) := by
  obtain ⟨j, hj⟩ : ∃ j, c.k = j + 1 := ⟨c.k - 1, by omega⟩
  simp [curTapeG, VR.tl, fld, hj, List.replicate_succ]

theorem curG_kw (w : VR) : w.curG.k = w.k ∧ w.curG.w = w.w := by
  by_cases h : w.O = 3 <;> simp [VR.curG, VR.cur, VR.dec, h] <;> split <;> simp_all

/-- The first record as cursor: `FAL` to the cursor tape of `passLoop`. -/
theorem faG' (L Pm : List Nat) (hL : NoB L) (hP : GoodW Pm) (w : VR) (hw : w.Ok) (ws : List VR)
    (hws : ∀ x ∈ ws, x.Ok) (hcmp : w.O = 3 → ∃ z, 1 ≤ w.k ∧ w.E = fld (w.k + z) w.k)
    (hLe : L = Pm ++ 1 :: 1 :: ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws))) :
    znttLogic.Reach (hd QNTT.FAL L [])
      (hd QNTT.RFL (curTapeG Pm [] w.curG 0 (w.k - 1) (w.w - w.k) (ws.map VR.dec)) []) := by
  have h := faG L Pm hL hP w hw ws hws hcmp hLe
  have hcur : w.curG.F = 3 := by
    by_cases h : w.O = 3 <;> simp [VR.curG, VR.cur, h]
  obtain ⟨k1, k2⟩ := curG_kw w
  have hOk : w.curG.k ≥ 1 := by rw [k1]; exact hw.k1
  have hkw : w.curG.k ≤ w.curG.w := by rw [k1, k2]; exact hw.kw
  have := curTapeG_tl Pm [] w.curG hOk hkw hcur (ws.map VR.dec)
  rw [k1, k2] at this
  rw [this]
  have hk : w.curG.O = w.O ∧ w.curG.P = w.P := by
    by_cases h : w.O = 3 <;> simp [VR.curG, VR.cur, VR.dec, h] <;> split <;> simp_all
  rw [hk.1, hk.2]
  simpa [tailB] using h


/-- A finished record, re-armed for the next pass with input flag `x`. -/
def VR.nextPass (c : VR) (x : Nat) : VR :=
  { F := 2, O := c.O, P := x, w := c.w, k := if x = 3 then 2 else 1, E := c.E, m := c.m, n := c.n, s := c.s,
    a := 0, c := c.a + c.c, t := c.t }

def VR.doneX (c : VR) (r s x : Nat) : Rc :=
  { F := 2, O := c.O, Pf := x, acc := List.replicate r 2 ++ 3 :: List.replicate s 2, E := c.E,
    b0 := c.b.headD 2, br := c.b.tail, u0 := c.u.headD 2, ur := c.u.tail }

theorem doneX_eq (c : VR) (r s x : Nat) : ({ c.done r s with Pf := x } : Rc) = c.doneX r s x := rfl

theorem done_ps_vr (c : VR) (hc : c.Ok) (r s x : Nat) (hrs : r + 1 + s = c.w) (hw2 : 2 ≤ c.w) (hx : x ∈ [2, 3]) :
    1 :: 1 :: (c.doneX r s x).ps.body = (c.nextPass x).recd := by
  have hrest : (c.doneX r s x).Rest := by
    have := VR.toRcA_rest c (List.replicate r 2 ++ 3 :: List.replicate s 2)
    simpa [VR.doneX, VR.toRcA, Rc.Rest] using this
  rw [Rc.ps_body _ hrest]
  have hB : (c.doneX r s x).b0 :: (c.doneX r s x).br = c.b := by
    obtain ⟨b0, br, hB⟩ := List.exists_cons_of_ne_nil hc.bne
    simp [VR.doneX, hB]
  have hU : (c.doneX r s x).u0 :: (c.doneX r s x).ur = c.u := by
    obtain ⟨u0, ur, hU⟩ := List.exists_cons_of_ne_nil hc.une
    simp [VR.doneX, hU]
  have hu : c.u = winStr c.a (c.c + 1) c.t := by simp [VR.u, winStr]
  have hlen : (c.doneX r s x).acc.length = c.w := by
    simp [VR.doneX]; omega
  have e1 : (c.doneX r s x).b0 :: ((c.doneX r s x).br ++ 1 :: restoreU ((c.doneX r s x).u0 :: (c.doneX r s x).ur)) =
      c.b ++ 1 :: (List.replicate (c.a + c.c + 1) 3 ++ List.replicate c.t 2) := by
    rw [hU, hu, restoreU_win _ _ _ (by omega)]
    rw [← hB]; simp; omega
  have hE : (c.doneX r s x).E = c.E := rfl
  have hO : (c.doneX r s x).O = c.O := rfl
  have hP : (c.doneX r s x).Pf = x := rfl
  rw [hE, hO, hP, hlen, accI_fld x _ hx hw2, e1]
  simp [VR.recd, VR.tl, VR.nextPass, VR.b, VR.u, List.replicate_succ]


theorem vis_P (v : VR) : v.vis.P = v.P := by unfold VR.vis; split <;> simp
theorem inc_P (v : VR) : v.inc.P = v.P := by simp [VR.inc]
theorem dec_P (v : VR) : v.dec.P = v.P := by unfold VR.dec; split <;> simp
theorem curG_P (v : VR) : v.curG.P = v.P := by
  unfold VR.curG VR.cur VR.dec; split <;> split <;> simp

theorem stepList_P : ∀ vs : List VR, (stepList vs).map VR.P = vs.map VR.P
  | [] => by simp [stepList]
  | v :: vs => by simp [stepList, vis_P, inc_P, Function.comp_def]

theorem stepN_P (r : Nat) : ∀ vs : List VR, (stepN r vs).map VR.P = vs.map VR.P := by
  induction r with
  | zero => intro vs; simp [stepN]
  | succ r ih => intro vs; rw [stepN, ih, stepList_P]

theorem vis_w (v : VR) : v.vis.w = v.w := by unfold VR.vis; split <;> simp
theorem inc_w (v : VR) : v.inc.w = v.w := by simp [VR.inc]
theorem dec_w (v : VR) : v.dec.w = v.w := by unfold VR.dec; split <;> simp
theorem stepList_w : ∀ vs : List VR, (stepList vs).map VR.w = vs.map VR.w
  | [] => by simp [stepList]
  | v :: vs => by simp [stepList, vis_w, inc_w, Function.comp_def]
theorem stepN_w (r : Nat) : ∀ vs : List VR, (stepN r vs).map VR.w = vs.map VR.w := by
  induction r with
  | zero => intro vs; simp [stepN]
  | succ r ih => intro vs; rw [stepN, ih, stepList_w]
theorem stepN_w2 (r : Nat) (vs : List VR) (h : ∀ x ∈ vs, 2 ≤ x.w) : ∀ x ∈ stepN r vs, 2 ≤ x.w := by
  intro x hx
  have h1 : x.w ∈ (stepN r vs).map VR.w := List.mem_map_of_mem hx
  rw [stepN_w] at h1
  simp only [List.mem_map] at h1
  obtain ⟨y, hy, he⟩ := h1
  rw [← he]; exact h y hy

def outRec (c : VR) (r : Nat) : VR :=
  if c.O = 2 then c else { c with E := fld c.E.length (eAdv c.E.length (r * c.n) (c.E.count 3)) }

def outP (c : VR) (r : Nat) (p : Nat × Nat) : Nat × Nat := if c.O = 2 then p else sAdv (r * c.n) p

structure LoopOut where
  cs : List (VR × Nat × Nat)
  c' : VR
  r' : Nat
  s' : Nat
  p' : Nat × Nat

/-- The pure run of a pass loop: the finished cursor records and the final cursor. -/
def loopRun : Nat → VR → List VR → Nat → Nat → Nat × Nat → LoopOut
  | 0, c, _, r, s, p => ⟨[], c, r, s, p⟩
  | n + 1, c, vs, r, s, p =>
    match stepN r vs with
    | [] => ⟨[], c, r, s, p⟩
    | w :: ws =>
      let o := loopRun n w.curG (ws.map VR.dec) (w.k - 1) (w.w - w.k) (outP c r p)
      ⟨(outRec c r, r, s) :: o.cs, o.c', o.r', o.s', o.p'⟩

theorem count3_fld (len e : Nat) (h : e ≤ len) : (fld len e).count 3 = e := by
  simp [fld, List.count_replicate]

/-- `passLoop` with the bookkeeping needed to chain passes: the finished records are `done` records. -/
theorem passLoop2 (Wf : List Nat) (hW : BitsD Wf) (P2 : List Nat) (hP2 : GoodW (1 :: P2)) :
    ∀ (n : Nat) (vs : List VR) (c : VR) (pre : List Rc) (p : Nat × Nat) (r s : Nat),
    r + 1 + s = c.w → vs.length = n → CurInv c → (∀ x ∈ vs, x.Ok) → OutM vs → PreOk pre → 1 ≤ p.2 → PassCmp n r vs → 2 ≤ c.w → (∀ x ∈ vs, 2 ≤ x.w) →
    ∃ (p' : Nat × Nat) (pre' : List Rc) (c' : VR) (r' s' : Nat) (cs : List (VR × Nat × Nat)), CurInv c' ∧ PreOk pre' ∧
      1 ≤ p'.2 ∧ r' + 1 + s' = c'.w ∧ 2 ≤ c'.w ∧ pre' = pre ++ cs.map (fun t => t.1.done t.2.1 t.2.2) ∧
      (∀ t ∈ cs, t.1.Ok ∧ t.2.1 + 1 + t.2.2 = t.1.w ∧ 2 ≤ t.1.w) ∧
      cs.map (fun t => t.1.P) ++ [c'.P] = c.P :: vs.map VR.P ∧
      loopRun n c vs r s p = ⟨cs, c', r', s', p'⟩ ∧
      znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: P2)) pre c 0 r s vs) [])
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p'.1 2 ++ List.replicate p'.2 3 ++ 1 :: P2)) pre' c' 0 r' s' []) []) := by
  intro n
  induction n with
  | zero =>
    intro vs c pre p r s hrs hlen hc hvs hom hpre hp hcmp hcw hvw
    have : vs = [] := List.length_eq_zero_iff.mp hlen
    subst this
    exact ⟨p, pre, c, r, s, [], hc, hpre, hp, hrs, hcw, by simp, by simp, by simp, by simp [loopRun], LTM.Reach.refl _ _⟩
  | succ n ih =>
    intro vs c pre p r s hrs hlen hc hvs hom hpre hp hcmp hcw hvw
    obtain ⟨hcOk, hF, hOut⟩ := hc
    have hlen' := stepN_length r vs
    obtain ⟨w, ws, hw⟩ : ∃ w ws, stepN r vs = w :: ws := by
      cases h : stepN r vs with
      | nil => rw [h] at hlen'; simp at hlen'; omega
      | cons w ws => exact ⟨w, ws, rfl⟩
    have hok := stepN_ok r vs hvs
    rw [hw] at hok
    have hwOk : w.Ok := hok w (by simp)
    have hwsOk : ∀ x ∈ ws, x.Ok := fun x hx => hok x (by simp [hx])
    have hout := stepN_outM r vs hom
    rw [hw] at hout
    have hwm : w.O = 3 → w.m = 0 := hout w (by simp)
    have hlenws : (ws.map VR.dec).length = n := by
      rw [hw] at hlen'; simp at hlen'; simp; omega
    have hcmp' : (w.O = 3 → ∃ z, 1 ≤ w.k ∧ w.E = fld (w.k + z) w.k) ∧ PassCmp n (w.k - 1) (ws.map VR.dec) := by
      have := hcmp; simp only [PassCmp, hw] at this; exact this
    have hinv := curG_inv w hwOk hwm
    have hrsw : w.k - 1 + 1 + (w.w - w.k) = w.curG.w := by
      have := (curG_kw w).2; have h1 := hwOk.k1; have h2 := hwOk.kw; omega
    have hwsOk' : ∀ x ∈ ws.map VR.dec, x.Ok := by
      intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx; exact y.dec_ok (hwsOk y hy)
    have homws : OutM (ws.map VR.dec) := dec_outM ws (fun x hx => hout x (by simp [hx]))
    have hwall := stepN_w2 r vs hvw
    rw [hw] at hwall
    have hcw2 : 2 ≤ w.curG.w := by rw [(curG_kw w).2]; exact hwall w (by simp)
    have hvw2 : ∀ x ∈ ws.map VR.dec, 2 ≤ x.w := by
      intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
      rw [dec_w]; exact hwall y (by simp [hy])
    have hPm := pm_good Wf P2 hW hP2 p hp
    by_cases hO : c.O = 2
    · have h1 := colStepN c hcOk hF hO _ hPm pre hpre r s vs hvs w ws hw hcmp'.1
      obtain ⟨p', pre', c', r', s', cs, hi, hp', hq, hrs', hcw', hpe, hcs, hPc, hRun, hr⟩ :=
        ih (ws.map VR.dec) w.curG (pre ++ [c.done r s]) p (w.k - 1) (w.w - w.k) hrsw hlenws hinv hwsOk' homws
          (preOk_done pre hpre c hcOk r s) hp hcmp'.2 hcw2 hvw2
      exact ⟨p', pre', c', r', s', (c, r, s) :: cs, hi, hp', hq, hrs', hcw', by simp [hpe],
        fun t ht => by simp at ht; rcases ht with rfl | ht; exact ⟨hcOk, hrs, hcw⟩; exact hcs t ht, (by
          have hs := stepN_P r vs
          rw [hw] at hs
          simp only [List.map_cons, List.cons_append]
          rw [hPc]
          simp only [List.map_cons] at hs
          simp [curG_P, Function.comp_def, dec_P, hs]), (by
          simp only [loopRun, hw]
          simp [outRec, outP, hO, hRun]), h1.trans hr⟩
    · have hO3 : c.O = 3 := by have := hcOk.O; simp at this; omega
      obtain ⟨hm, e, he, hew, hE⟩ := hOut hO3
      have hElen := hcOk.Elen
      have h1 := colStepO c.n c hcOk hF hO3 hm rfl Wf hW P2 hP2 pre hpre s c.E.length hElen r p e hp he hew hE vs hvs w ws
        hw hcmp'.1
      have hb := eAdv_bounds c.E.length (r * c.n) e he hew
      have hc' : ({ c with E := fld c.E.length (eAdv c.E.length (r * c.n) e) } : VR).Ok :=
        { F := hcOk.F, O := hcOk.O, P := hcOk.P, k1 := hcOk.k1, kw := hcOk.kw, E := fld_bits _ _,
          Elen := by show 2 ≤ (fld c.E.length (eAdv c.E.length (r * c.n) e)).length; rw [fld_len _ _ hb.2]; exact hElen,
          Elw := by show (fld c.E.length (eAdv c.E.length (r * c.n) e)).length = _; rw [fld_len _ _ hb.2]; exact hcOk.Elw }
      obtain ⟨p', pre', c', r', s', cs, hi, hp', hq, hrs', hcw', hpe, hcs, hPc, hRun, hr⟩ :=
        ih (ws.map VR.dec) w.curG _ (sAdv (r * c.n) p) (w.k - 1) (w.w - w.k) hrsw hlenws hinv hwsOk' homws
          (preOk_done pre hpre _ hc' r s) (sAdv_pos _ p hp) hcmp'.2 hcw2 hvw2
      exact ⟨p', pre', c', r', s', (({ c with E := fld c.E.length (eAdv c.E.length (r * c.n) e) } : VR), r, s) :: cs,
        hi, hp', hq, hrs', hcw', by simp [hpe],
        fun t ht => by simp at ht; rcases ht with rfl | ht; exact ⟨hc', hrs, hcw⟩; exact hcs t ht, (by
          have hs := stepN_P r vs
          rw [hw] at hs
          simp only [List.map_cons, List.cons_append]
          rw [hPc]
          simp only [List.map_cons] at hs
          simp [curG_P, Function.comp_def, dec_P, hs]), (by
          have hcount : c.E.count 3 = e := by
            have := count3_fld c.E.length e hew
            rw [← hE] at this; exact this
          simp only [loopRun, hw]
          simp [outRec, outP, hO, hRun, hcount]), h1.trans hr⟩




/-- One whole evaluation pass, ending in the check `SC` (more passes follow: `Nn = 1^(a+2) 0^b`). -/
theorem passMore2 (Wf : List Nat) (hW : BitsD Wf) (Q : List Nat) (a b : Nat)
    (hP2 : GoodW (1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2))) :
    ∀ (n : Nat) (vs : List VR) (c : VR) (pre : List Rc) (p : Nat × Nat) (r s : Nat),
    r + 1 + s = c.w → vs.length = n → CurInv c → (∀ x ∈ vs, x.Ok) → OutM vs → PreOk pre → 1 ≤ p.2 → PassCmp n r vs → 2 ≤ c.w → (∀ x ∈ vs, 2 ≤ x.w) →
    ∃ (p' : Nat × Nat) (pre' : List Rc) (cs : List (VR × Nat × Nat)), PreOk pre' ∧ pre' ≠ [] ∧ 1 ≤ p'.2 ∧
      pre' = pre ++ cs.map (fun t => t.1.done t.2.1 t.2.2) ∧ (∀ t ∈ cs, t.1.Ok ∧ t.2.1 + 1 + t.2.2 = t.1.w ∧ 2 ≤ t.1.w) ∧
      cs.map (fun t => t.1.P) = c.P :: vs.map VR.P ∧
      (∃ lo : LoopOut, loopRun n c vs r s p = lo ∧ cs = lo.cs ++ [(outRec lo.c' lo.r', lo.r', lo.s')] ∧
        p' = outP lo.c' lo.r' lo.p') ∧
      znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
          pre c 0 r s vs) [])
        (hd QNTT.SC (Wf ++ 1 :: (List.replicate p'.1 2 ++ List.replicate p'.2 3 ++ 1 :: Q) ++ List.replicate a 3)
          (3 :: 2 :: (List.replicate b 2 ++ tailB pre')) ) := by
  intro n vs c pre p r s hrs hlen hc hvs hom hpre hp hcmp hcw hvw
  obtain ⟨p', pre', c', r', s', cs, hc', hpre', hp', hrs', hcw', hpe, hcs, hPc, hRun, h1⟩ :=
    passLoop2 Wf hW (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2) hP2 n vs c pre p r s hrs hlen hc hvs hom hpre hp hcmp hcw hvw
  obtain ⟨hcOk, hF, hOut⟩ := hc'
  have finish : ∀ (p'' : Nat × Nat) (pre'' : List Rc), PreOk pre'' → pre'' ≠ [] → 1 ≤ p''.2 →
      znttLogic.Reach
        (hd QNTT.PE0 ((Wf ++ 1 :: (List.replicate p''.1 2 ++ List.replicate p''.2 3 ++ 1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2))) ++
          tailB pre'') [])
        (hd QNTT.SC (Wf ++ 1 :: (List.replicate p''.1 2 ++ List.replicate p''.2 3 ++ 1 :: Q) ++ List.replicate a 3)
          (3 :: 2 :: (List.replicate b 2 ++ tailB pre''))) := by
    intro p'' pre'' hpre'' hne hp''
    obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hG := pm_good Wf (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2) hW hP2 p'' hp''
    have hxs : ∀ y ∈ x :: xs, y.Ok := fun y hy => (hpre'' y hy).1
    have hrest : NoB (x.body ++ tailB xs) := by
      have := tailB_noB (x :: xs) hxs
      simp only [tailB, NoB_cons_iff] at this
      exact this.2.2
    have h := peMore (Wf ++ 1 :: (List.replicate p''.1 2 ++ List.replicate p''.2 3 ++ 1 :: Q)) a b
      (x.body ++ tailB xs) (by simpa [List.append_assoc] using hG) hrest
    simpa [tailB, List.append_assoc] using h
  by_cases hO : c'.O = 2
  · have hPm := pm_good Wf (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2) hW hP2 p' hp'
    have h2 := lastStepN c' hcOk hF hO _ hPm pre' hpre' r' s'
    exact ⟨p', pre' ++ [c'.done r' s'], cs ++ [(c', r', s')], preOk_done pre' hpre' c' hcOk r' s', by simp, hp',
      by simp [hpe], fun t ht => by simp at ht; rcases ht with ht | rfl; exact hcs t ht; exact ⟨hcOk, hrs', hcw'⟩, (by simpa using hPc), ⟨⟨cs, c', r', s', p'⟩, hRun, by simp [outRec, hO], by simp [outP, hO]⟩, h1.trans
      (h2.trans (finish p' _ (preOk_done pre' hpre' c' hcOk r' s') (by simp) hp'))⟩
  · have hO3 : c'.O = 3 := by have := hcOk.O; simp at this; omega
    obtain ⟨hm, e, he, hew, hE⟩ := hOut hO3
    have hElen := hcOk.Elen
    have h2 := lastStepO c'.n c' hcOk hF hO3 hm rfl Wf hW (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2) hP2
      pre' hpre' s' c'.E.length hElen r' p' e hp' he hew hE
    have hb := eAdv_bounds c'.E.length (r' * c'.n) e he hew
    have hElen' := hcOk.Elen
    rw [hE, fld_len _ _ hew] at hElen'
    have hc'' : ({ c' with E := fld c'.E.length (eAdv c'.E.length (r' * c'.n) e) } : VR).Ok :=
      { F := hcOk.F, O := hcOk.O, P := hcOk.P, k1 := hcOk.k1, kw := hcOk.kw, E := fld_bits _ _,
        Elen := by show 2 ≤ (fld c'.E.length (eAdv c'.E.length (r' * c'.n) e)).length; rw [fld_len _ _ hb.2]; exact hElen',
        Elw := by show (fld c'.E.length (eAdv c'.E.length (r' * c'.n) e)).length = _; rw [fld_len _ _ hb.2]; exact hcOk.Elw }
    have hpo := preOk_done pre' hpre' _ hc'' r' s'
    exact ⟨sAdv (r' * c'.n) p', _, cs ++ [(({ c' with E := fld c'.E.length (eAdv c'.E.length (r' * c'.n) e) } : VR), r', s')],
      hpo, by simp, sAdv_pos _ p' hp', by simp [hpe], fun t ht => by simp at ht; rcases ht with ht | rfl; exact hcs t ht; exact ⟨hc'', hrs', hcw'⟩, (by simpa using hPc), ⟨⟨cs, c', r', s', p'⟩, hRun, by
        have hcount : c'.E.count 3 = e := by
          have := count3_fld c'.E.length e hew
          rw [← hE] at this; exact this
        simp [outRec, hO, hcount], by simp [outP, hO]⟩, h1.trans (h2.trans (finish _ _ hpo (by simp) (sAdv_pos _ p' hp')))⟩


/-- One whole evaluation pass, the last one (`Nn = 1 0^b`), ending in `FL0`. -/
theorem passLast2 (Wf : List Nat) (hW : BitsD Wf) (Q : List Nat) (b : Nat)
    (hP2 : GoodW (1 :: (Q ++ [1] ++ [3] ++ List.replicate b 2))) :
    ∀ (n : Nat) (vs : List VR) (c : VR) (pre : List Rc) (p : Nat × Nat) (r s : Nat),
    r + 1 + s = c.w → vs.length = n → CurInv c → (∀ x ∈ vs, x.Ok) → OutM vs → PreOk pre → 1 ≤ p.2 → PassCmp n r vs → 2 ≤ c.w → (∀ x ∈ vs, 2 ≤ x.w) →
    ∃ (p' : Nat × Nat) (pre' : List Rc) (cs : List (VR × Nat × Nat)), PreOk pre' ∧ pre' ≠ [] ∧ 1 ≤ p'.2 ∧
      pre' = pre ++ cs.map (fun t => t.1.done t.2.1 t.2.2) ∧ (∀ t ∈ cs, t.1.Ok ∧ t.2.1 + 1 + t.2.2 = t.1.w ∧ 2 ≤ t.1.w) ∧
      cs.map (fun t => t.1.P) = c.P :: vs.map VR.P ∧
      (∃ lo : LoopOut, loopRun n c vs r s p = lo ∧ cs = lo.cs ++ [(outRec lo.c' lo.r', lo.r', lo.s')] ∧
        p' = outP lo.c' lo.r' lo.p') ∧
      znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: (Q ++ [1] ++ [3] ++ List.replicate b 2)))
          pre c 0 r s vs) [])
        (hd QNTT.FL0 (Wf ++ 1 :: (List.replicate p'.1 2 ++ List.replicate p'.2 3 ++ 1 :: Q))
          (1 :: 2 :: (List.replicate b 2 ++ tailB pre'))) := by
  intro n vs c pre p r s hrs hlen hc hvs hom hpre hp hcmp hcw hvw
  obtain ⟨p', pre', c', r', s', cs, hc', hpre', hp', hrs', hcw', hpe, hcs, hPc, hRun, h1⟩ :=
    passLoop2 Wf hW (Q ++ [1] ++ [3] ++ List.replicate b 2) hP2 n vs c pre p r s hrs hlen hc hvs hom hpre hp hcmp hcw hvw
  obtain ⟨hcOk, hF, hOut⟩ := hc'
  have finish : ∀ (p'' : Nat × Nat) (pre'' : List Rc), PreOk pre'' → pre'' ≠ [] → 1 ≤ p''.2 →
      znttLogic.Reach
        (hd QNTT.PE0 ((Wf ++ 1 :: (List.replicate p''.1 2 ++ List.replicate p''.2 3 ++ 1 :: (Q ++ [1] ++ [3] ++ List.replicate b 2))) ++
          tailB pre'') [])
        (hd QNTT.FL0 (Wf ++ 1 :: (List.replicate p''.1 2 ++ List.replicate p''.2 3 ++ 1 :: Q))
          (1 :: 2 :: (List.replicate b 2 ++ tailB pre''))) := by
    intro p'' pre'' hpre'' hne hp''
    obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hG := pm_good Wf (Q ++ [1] ++ [3] ++ List.replicate b 2) hW hP2 p'' hp''
    have hxs : ∀ y ∈ x :: xs, y.Ok := fun y hy => (hpre'' y hy).1
    have hrest : NoB (x.body ++ tailB xs) := by
      have := tailB_noB (x :: xs) hxs
      simp only [tailB, NoB_cons_iff] at this
      exact this.2.2
    have h := peLast (Wf ++ 1 :: (List.replicate p''.1 2 ++ List.replicate p''.2 3 ++ 1 :: Q)) b
      (x.body ++ tailB xs) (by simpa [List.append_assoc] using hG) hrest
    simpa [tailB, List.append_assoc] using h
  by_cases hO : c'.O = 2
  · have hPm := pm_good Wf (Q ++ [1] ++ [3] ++ List.replicate b 2) hW hP2 p' hp'
    have h2 := lastStepN c' hcOk hF hO _ hPm pre' hpre' r' s'
    exact ⟨p', pre' ++ [c'.done r' s'], cs ++ [(c', r', s')], preOk_done pre' hpre' c' hcOk r' s', by simp, hp',
      by simp [hpe], fun t ht => by simp at ht; rcases ht with ht | rfl; exact hcs t ht; exact ⟨hcOk, hrs', hcw'⟩, (by simpa using hPc), ⟨⟨cs, c', r', s', p'⟩, hRun, by simp [outRec, hO], by simp [outP, hO]⟩, h1.trans
      (h2.trans (finish p' _ (preOk_done pre' hpre' c' hcOk r' s') (by simp) hp'))⟩
  · have hO3 : c'.O = 3 := by have := hcOk.O; simp at this; omega
    obtain ⟨hm, e, he, hew, hE⟩ := hOut hO3
    have hElen := hcOk.Elen
    have h2 := lastStepO c'.n c' hcOk hF hO3 hm rfl Wf hW (Q ++ [1] ++ [3] ++ List.replicate b 2) hP2
      pre' hpre' s' c'.E.length hElen r' p' e hp' he hew hE
    have hb := eAdv_bounds c'.E.length (r' * c'.n) e he hew
    have hElen' := hcOk.Elen
    rw [hE, fld_len _ _ hew] at hElen'
    have hc'' : ({ c' with E := fld c'.E.length (eAdv c'.E.length (r' * c'.n) e) } : VR).Ok :=
      { F := hcOk.F, O := hcOk.O, P := hcOk.P, k1 := hcOk.k1, kw := hcOk.kw, E := fld_bits _ _,
        Elen := by show 2 ≤ (fld c'.E.length (eAdv c'.E.length (r' * c'.n) e)).length; rw [fld_len _ _ hb.2]; exact hElen',
        Elw := by show (fld c'.E.length (eAdv c'.E.length (r' * c'.n) e)).length = _; rw [fld_len _ _ hb.2]; exact hcOk.Elw }
    have hpo := preOk_done pre' hpre' _ hc'' r' s'
    exact ⟨sAdv (r' * c'.n) p', _, cs ++ [(({ c' with E := fld c'.E.length (eAdv c'.E.length (r' * c'.n) e) } : VR), r', s')],
      hpo, by simp, sAdv_pos _ p' hp', by simp [hpe], fun t ht => by simp at ht; rcases ht with ht | rfl; exact hcs t ht; exact ⟨hc'', hrs', hcw'⟩, (by simpa using hPc), ⟨⟨cs, c', r', s', p'⟩, hRun, by
        have hcount : c'.E.count 3 = e := by
          have := count3_fld c'.E.length e hew
          rw [← hE] at this; exact this
        simp [outRec, hO, hcount], by simp [outP, hO]⟩, h1.trans (h2.trans (finish _ _ hpo (by simp) (sAdv_pos _ p' hp')))⟩


theorem goodW_inv {x : Nat} {l : List Nat} (h : GoodW (x :: l)) :
    (x ∈ [2, 3] ∧ GoodW l) ∨ (x = 1 ∧ ∃ c w, l = c :: w ∧ c ∈ [2, 3] ∧ GoodW w) := by
  cases h with
  | bit hb h' => exact Or.inl ⟨hb, h'⟩
  | mb hb h' => exact Or.inr ⟨rfl, _, _, rfl, hb, h'⟩

theorem goodW_swap_tail : ∀ (n : Nat) (u : List Nat) (b b' : Nat) (v1 v2 : List Nat), u.length = n →
    b ∈ [2, 3] → b' ∈ [2, 3] → BitsD v1 → BitsD v2 →
    GoodW (u ++ b :: v1) → GoodW (u ++ b' :: v2) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro u b b' v1 v2 hn hb hb' h1 h2 h
    cases u with
    | nil => exact GoodW.bit hb' (GoodW.bits h2)
    | cons x u =>
      simp only [List.cons_append] at h ⊢
      rcases goodW_inv h with ⟨hx, h'⟩ | ⟨rfl, c, w, hw, hc, h'⟩
      · exact GoodW.bit hx (ih u.length (by simp at hn; omega) u b b' v1 v2 rfl hb hb' h1 h2 h')
      · cases u with
        | nil =>
          exact GoodW.mb hb' (GoodW.bits h2)
        | cons c' u' =>
          simp only [List.cons_append, List.cons.injEq] at hw
          obtain ⟨rfl, rfl⟩ := hw
          exact GoodW.mb hc (ih u'.length (by simp at hn; omega) u' b b' v1 v2 rfl hb hb' h1 h2 h')


/-- After a non-final pass with `S = 0` (`p'.1 = 0`): the check `SC` passes, the input flag moves on, and we are back in `RZ1`. -/
theorem scBridge (Wf : List Nat) (hW : BitsD Wf) (Q : List Nat) (a b q : Nat)
    (hP2 : GoodW (1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
    (pre0 : List Rc) (hpre0 : ∀ x ∈ pre0, x.Ok ∧ x.acc ≠ [] ∧ x.Pf = 2) (r r2 : Rc) (hr : r.Ok) (hacc : r.acc ≠ [])
    (h3 : r.Pf = 3) (hr2 : r2.Ok) (post : List Rc) (hpost : ∀ x ∈ post, x.Ok) :
    znttLogic.Reach
      (hd QNTT.SC (Wf ++ 1 :: (List.replicate q 3 ++ 1 :: Q) ++ List.replicate a 3)
        (3 :: 2 :: (List.replicate b 2 ++ tailB (pre0 ++ r :: r2 :: post))))
      (hdR QNTT.RZ1 [] (Wf ++ 1 :: (List.replicate q 3 ++ 1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2)) ++
        tailB (pre0 ++ { r with Pf := 2 } :: { r2 with Pf := 3 } :: post))) := by
  have hG : GoodW (1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2)) := by
    have := goodW_swap_tail (1 :: (Q ++ List.replicate a 3)).length (1 :: (Q ++ List.replicate a 3)) 3 3
      (3 :: List.replicate b 2) (2 :: List.replicate b 2) rfl (by simp) (by simp)
      (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all [List.mem_replicate])
      (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all [List.mem_replicate])
      (by
        have e : (1 :: (Q ++ List.replicate a 3)) ++ 3 :: 3 :: List.replicate b 2 =
            1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2) := by
          simp [List.replicate_succ, List.append_assoc]
          have key : ∀ (a : Nat) (L : List Nat), List.replicate a 3 ++ 3 :: L = 3 :: (List.replicate a 3 ++ L) := by
            intro a L; induction a with
            | zero => simp
            | succ a ih => simp [List.replicate_succ, ih]
          rw [key, key]
        rw [e]; exact hP2)
    simpa [List.append_assoc] using this
  have nP := hP2.noB
  simp only [NoB_cons_iff, NoB_app_iff] at nP
  have n3 : (3 : Nat) ∈ NB := by simp [NB]
  have n1 : (1 : Nat) ∈ NB := by simp [NB]
  have hnX : NoB (Wf ++ 1 :: (List.replicate q 3 ++ 1 :: Q) ++ List.replicate a 3) := by
    simp only [NoB_cons_iff, NoB_app_iff]
    exact ⟨⟨hW.noB, n1, noB_rep q 3 (by simp), n1, nP.2.1.1⟩, noB_rep a 3 (by simp)⟩
  have hsY : Sym4 (3 :: 2 :: (List.replicate b 2 ++ tailB (pre0 ++ r :: r2 :: post))) := by
    have sT : Sym4 (tailB (pre0 ++ r :: r2 :: post)) := tailB_sym4 _ (fun x hx => by
      simp only [List.mem_append, List.mem_cons] at hx
      rcases hx with hx | rfl | rfl | hx
      · exact (hpre0 x hx).1
      · exact hr
      · exact hr2
      · exact hpost x hx)
    have s2 : Sym4 (List.replicate b 2) := (BitsD.rep b 2 (by simp)).sym4
    exact Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) (s2.app sT))
  have := scPm Wf hW q (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2) hG pre0 hpre0 r r2 hr hacc h3 hr2 post hpost
    _ _ (by simp [List.append_assoc]) hnX hsY
  simpa [List.append_assoc] using this


/-- After a non-final pass with `S ≠ 0` (it starts with a `0`): refuted, `ODL` with the tape unchanged on the right. -/
theorem scFail (Wf : List Nat) (hW : BitsD Wf) (S' T X Y : List Nat) (hS : BitsD S') (hT : Sym4 T)
    (hXY : X ++ Y = Wf ++ 1 :: (2 :: S' ++ T)) (hX : NoB X) (hY : Sym4 Y) :
    znttLogic.Reach (hd QNTT.SC X Y) (hd QNTT.ODL (Wf ++ [1]) (2 :: (S' ++ T))) := by
  have sW := hW.sym4
  have sS : Sym4 S' := hS.sym4
  have a2 : (2 : Nat) ∈ ALL := by simp [ALL]
  have a1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have h0 := sc0Scan X Y hX hY
  rw [hXY] at h0
  have b1 := sc1Block [] Wf (1 :: (2 :: S' ++ T)) Sym4.nil hW (by simp [*])
  have b2 := sc1M ([] ++ Wf) (2 :: S' ++ T) (by simp [*]) (by simp [*])
  have b3 := sc2Zero ([] ++ Wf ++ [1]) (S' ++ T) (by simp [*]) (by simp [*])
  simp only [List.nil_append, List.append_assoc, List.cons_append] at h0 b1 b2 b3 ⊢
  exact h0.trans (b1.trans (b2.trans b3))


theorem goodW_rest : ∀ {u : List Nat}, GoodW u → ∃ v, Rest u v := by
  intro u h
  induction h with
  | nil => exact ⟨[], Rest.nil⟩
  | bit hb _ ih => obtain ⟨v, hv⟩ := ih; exact ⟨_, Rest.bit hb hv⟩
  | mb hb _ ih => obtain ⟨v, hv⟩ := ih; exact ⟨_, Rest.mb hb hv⟩


/-- A failed assignment: from `ODL` on `Pm ++ 1 :: 1 :: tapeL (o :: os)` to the next assignment (`WI0`) or the overflow `BEEP`. -/
theorem odFail (u : List Nat) (hu : GoodW u) (o : ORec) (os : List ORec) (hos : ∀ x ∈ o :: os, x.Ok)
    (L R : List Nat) (hXY : L ++ R = u ++ 1 :: 1 :: tapeL (o :: os)) (hL : NoB L) (hR : Sym4 R) :
    ∃ v, Rest u v ∧
      (∀ os', odoStepR (o :: os) = some os' → ∃ X R', X ++ 3 :: R' = (v ++ [1, 1]) ++ tapeL os' ∧
        znttLogic.Reach (hd QNTT.ODL L R) (hd QNTT.WI0 X (3 :: R'))) ∧
      (odoStepR (o :: os) = none →
        znttLogic.Reach (hd QNTT.ODL L R) (hd QNTT.BEEP ((v ++ [1, 1]) ++ tapeL (resetAll (o :: os))) [])) := by
  obtain ⟨v, hv⟩ := goodW_rest hu
  refine ⟨v, hv, ?_⟩
  have sT : Sym4 (tapeL (o :: os)) := tapeL_sym4 _ (fun x hx => hos x hx)
  have a1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have s1 : Sym4 (1 :: tapeL (o :: os)) := Sym4.cons a1 sT
  have h0 := odlScan L R hL hR
  rw [hXY] at h0
  have h1 := od0Walk hv [] (1 :: 1 :: tapeL (o :: os)) Sym4.nil (Sym4.cons a1 s1)
  have h2 := od0M ([] ++ v) (1 :: tapeL (o :: os)) (by simpa using hv.sym4_dst) s1
  have h3 := od0mM ([] ++ v ++ [1]) (tapeL (o :: os)) (by simpa using hv.sym4_dst.app (sym4_cell 1 (by simp))) sT
  have hw := odoWalk os o ([] ++ v ++ [1] ++ [1]) hos
    (by simpa using hv.sym4_dst.app (Sym4.cons a1 (Sym4.cons a1 Sym4.nil)))
  simp only [List.nil_append, List.append_assoc, List.cons_append] at h0 h1 h2 h3 hw ⊢
  have hc := h0.trans (h1.trans (h2.trans h3))
  refine ⟨fun os' h => ?_, fun h => ?_⟩
  · obtain ⟨X, R', e, hr⟩ := hw.1 os' h
    exact ⟨X, R', by simpa using e, hc.trans hr⟩
  · have := hw.2 h
    simpa using hc.trans this


/-- A record list whose flags read `2^j 3 x :: l` splits around the input flag. -/
theorem flagSplit : ∀ (j : Nat) (pre : List Rc) (l : List Nat), pre.map Rc.Pf = List.replicate j 2 ++ 3 :: l → l ≠ [] →
    ∃ pre0 r r2 post, pre = pre0 ++ r :: r2 :: post ∧ (∀ x ∈ pre0, x.Pf = 2) ∧ r.Pf = 3 := by
  intro j
  induction j with
  | zero =>
    intro pre l h hl
    cases pre with
    | nil => simp at h
    | cons r rs =>
      cases rs with
      | nil => simp at h; simp [h] at hl
      | cons r2 post =>
        simp [List.replicate] at h
        exact ⟨[], r, r2, post, by simp, by simp, h.1⟩
  | succ j ih =>
    intro pre l h hl
    cases pre with
    | nil => simp [List.replicate_succ] at h
    | cons x rs =>
      simp only [List.replicate_succ, List.map_cons, List.cons_append, List.cons.injEq] at h
      obtain ⟨hx, h'⟩ := h
      obtain ⟨pre0, r, r2, post, he, h0, h3⟩ := ih rs l h' hl
      refine ⟨x :: pre0, r, r2, post, by simp [he], ?_, h3⟩
      intro y hy; simp at hy; rcases hy with rfl | hy
      · exact hx
      · exact h0 y hy


/-- `SC` after a pass with `S = 0`, given the flag pattern of the finished records. -/
theorem scStep (Wf : List Nat) (hW : BitsD Wf) (Q : List Nat) (a b q : Nat)
    (hP2 : GoodW (1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
    (pre : List Rc) (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ []) (j : Nat) (l : List Nat)
    (hfl : pre.map Rc.Pf = List.replicate j 2 ++ 3 :: l) (hl : l ≠ []) :
    ∃ pre0 r r2 post, pre = pre0 ++ r :: r2 :: post ∧ (∀ x ∈ pre0, x.Pf = 2) ∧ r.Pf = 3 ∧
      znttLogic.Reach
        (hd QNTT.SC (Wf ++ 1 :: (List.replicate q 3 ++ 1 :: Q) ++ List.replicate a 3)
          (3 :: 2 :: (List.replicate b 2 ++ tailB pre)))
        (hdR QNTT.RZ1 [] (Wf ++ 1 :: (List.replicate q 3 ++ 1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2)) ++
          tailB (pre0 ++ { r with Pf := 2 } :: { r2 with Pf := 3 } :: post))) := by
  obtain ⟨pre0, r, r2, post, he, h0, h3⟩ := flagSplit j pre l hfl hl
  refine ⟨pre0, r, r2, post, he, h0, h3, ?_⟩
  have mem : ∀ x, x ∈ pre0 ∨ x = r ∨ x = r2 ∨ x ∈ post → x ∈ pre := by
    intro x hx; rw [he]; simpa using hx
  have := scBridge Wf hW Q a b q hP2 pre0 (fun x hx => ⟨(hpre x (mem x (Or.inl hx))).1, (hpre x (mem x (Or.inl hx))).2, h0 x hx⟩)
    r r2 (hpre r (mem r (Or.inr (Or.inl rfl)))).1 (hpre r (mem r (Or.inr (Or.inl rfl)))).2 h3
    (hpre r2 (mem r2 (Or.inr (Or.inr (Or.inl rfl))))).1 post (fun x hx => (hpre x (mem x (Or.inr (Or.inr (Or.inr hx))))).1)
  rw [he]; exact this


/-- The pass start from `RZ1` at the left end. -/
theorem passStartRZ1 (Pm : List Nat) (hP : GoodW Pm) (r : Rc) (hr : r.PS)
    (rs : List Rc) (hrs : ∀ x ∈ rs, x.PS) :
    znttLogic.Reach (hdR QNTT.RZ1 [] (Pm ++ 1 :: 1 :: (r.body ++ tailB rs)))
      (hd QNTT.FAL (Pm ++ [1, 1] ++ r.ps.body ++ tailP rs) []) := by
  have sT : Sym4 (r.body ++ tailB rs) :=
    (r.body_sym4 hr.ok).app (tailB_sym4 rs (fun x hx => (hrs x hx).ok))
  have h2 := rz1Good hP [] (1 :: 1 :: (r.body ++ tailB rs)) Sym4.nil (sym4_M (sym4_M sT))
  have h3 := rz1MM Pm (r.body ++ tailB rs) hP.sym4 sT
  have h4 := passStart rs hrs r hr (Pm ++ [1, 1]) (hP.sym4.app (sym4_M (sym4_M Sym4.nil)))
  simp only [List.nil_append, List.append_assoc, List.cons_append, List.append_nil] at h2 h3 h4 ⊢
  exact h2.trans (h3.trans h4)


theorem Rc.PS.withPf {r : Rc} (h : r.PS) (x : Nat) (hx : x ∈ [2, 3]) : ({ r with Pf := x } : Rc).PS :=
  { ok := { h.ok with Pf := hx }, acc2 := h.acc2, rest := h.rest }

/-- From `SC` after a pass with `S = 0` to the start of the next pass (`FAL`). -/
theorem scStart (Wf : List Nat) (hW : BitsD Wf) (Q : List Nat) (a b q : Nat)
    (hP2 : GoodW (1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
    (pre : List Rc) (hps : ∀ x ∈ pre, x.PS) (j : Nat) (l : List Nat)
    (hfl : pre.map Rc.Pf = List.replicate j 2 ++ 3 :: l) (hl : l ≠ []) (hq : 1 ≤ q) :
    ∃ pre0 r r2 post r0 rs, pre = pre0 ++ r :: r2 :: post ∧ (∀ x ∈ pre0, x.Pf = 2) ∧ r.Pf = 3 ∧
      pre0 ++ { r with Pf := 2 } :: { r2 with Pf := 3 } :: post = r0 :: rs ∧
      znttLogic.Reach
        (hd QNTT.SC (Wf ++ 1 :: (List.replicate q 3 ++ 1 :: Q) ++ List.replicate a 3)
          (3 :: 2 :: (List.replicate b 2 ++ tailB pre)))
        (hd QNTT.FAL ((Wf ++ 1 :: (List.replicate q 3 ++ 1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2))) ++
          [1, 1] ++ r0.ps.body ++ tailP rs) []) := by
  obtain ⟨pre0, r, r2, post, he, hp0, hp3, h1⟩ := scStep Wf hW Q a b q hP2 pre
    (fun x hx => ⟨(hps x hx).ok, fun h => by have := (hps x hx).acc2; simp [h] at this⟩) j l hfl hl
  have mem : ∀ x, (x ∈ pre0 ∨ x = r ∨ x = r2 ∨ x ∈ post) → x ∈ pre := by
    intro x hx; rw [he]; simpa using hx
  have hpsN : ∀ x ∈ pre0 ++ { r with Pf := 2 } :: { r2 with Pf := 3 } :: post, x.PS := by
    intro x hx
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | rfl | hx
    · exact hps x (mem x (Or.inl hx))
    · exact (hps r (mem r (Or.inr (Or.inl rfl)))).withPf 2 (by simp)
    · exact (hps r2 (mem r2 (Or.inr (Or.inr (Or.inl rfl))))).withPf 3 (by simp)
    · exact hps x (mem x (Or.inr (Or.inr (Or.inr hx))))
  obtain ⟨r0, rs, hr0⟩ : ∃ r0 rs, pre0 ++ { r with Pf := 2 } :: { r2 with Pf := 3 } :: post = r0 :: rs := by
    cases pre0 with
    | nil => exact ⟨_, _, rfl⟩
    | cons x xs => exact ⟨x, xs ++ { r with Pf := 2 } :: { r2 with Pf := 3 } :: post, rfl⟩
  refine ⟨pre0, r, r2, post, r0, rs, he, hp0, hp3, hr0, ?_⟩
  have hGP : GoodW (Wf ++ 1 :: (List.replicate q 3 ++ 1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2))) := by
    have hG : GoodW (1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2)) := by
      have := goodW_swap_tail (1 :: (Q ++ List.replicate a 3)).length (1 :: (Q ++ List.replicate a 3)) 3 3
        (3 :: List.replicate b 2) (2 :: List.replicate b 2) rfl (by simp) (by simp)
        (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all)
        (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all)
        (by
          have e : (1 :: (Q ++ List.replicate a 3)) ++ 3 :: 3 :: List.replicate b 2 =
              1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2) := by
            simp only [List.replicate_succ, List.cons_append, List.append_assoc, List.nil_append]
            have key : ∀ (a : Nat) (L : List Nat), List.replicate a 3 ++ 3 :: L = 3 :: (List.replicate a 3 ++ L) := by
              intro a L; induction a with
              | zero => simp
              | succ a ih => simp [List.replicate_succ, ih]
            rw [key, key]
          rw [e]; exact hP2)
      simpa [List.append_assoc] using this
    exact goodW_reg Wf (List.replicate q 3) _ hW (BitsD.rep q 3 (by simp))
      (by intro h; have := congrArg List.length h; simp at this; omega) hG
  have h2 := passStartRZ1 _ hGP r0 (hpsN r0 (by rw [hr0]; simp)) rs (fun x hx => hpsN x (by rw [hr0]; simp [hx]))
  rw [hr0] at h1
  simp only [tailB, List.append_assoc, List.cons_append] at h1 h2 ⊢
  exact h1.trans h2


theorem VR.nextPass_ok (c : VR) (hc : c.Ok) (x : Nat) (hx : x ∈ [2, 3]) (hw2 : 2 ≤ c.w) : (c.nextPass x).Ok :=
  { F := by simp [VR.nextPass], O := hc.O, P := hx,
    k1 := by simp only [VR.nextPass]; split <;> omega,
    kw := by simp only [VR.nextPass]; split <;> omega,
    E := hc.E, Elen := hc.Elen, Elw := hc.Elw }

theorem tailVR_doneX : ∀ l : List ((VR × Nat × Nat) × Nat),
    (∀ p ∈ l, p.1.1.Ok ∧ p.1.2.1 + 1 + p.1.2.2 = p.1.1.w ∧ 2 ≤ p.1.1.w ∧ p.2 ∈ [2, 3]) →
    tailP (l.map fun p => p.1.1.doneX p.1.2.1 p.1.2.2 p.2) = tailVR (l.map fun p => p.1.1.nextPass p.2)
  | [], _ => by simp [tailP, tailVR]
  | p :: l, h => by
    have hp := h p (by simp)
    have := done_ps_vr p.1.1 hp.1 p.1.2.1 p.1.2.2 p.2 hp.2.1 hp.2.2.1 hp.2.2.2
    have ih := tailVR_doneX l (fun q hq => h q (by simp [hq]))
    simp only [List.map_cons, tailP, tailVR, List.flatten_cons]
    simp only [tailVR] at ih
    rw [ih, ← this]
    simp


/-- The start of the next pass: from `FAL` on the finished records (with their new input flags) to the first cursor. -/
theorem faNext (Pm : List Nat) (hP : GoodW Pm) (t0 : (VR × Nat × Nat) × Nat) (ts : List ((VR × Nat × Nat) × Nat))
    (h : ∀ p ∈ t0 :: ts, p.1.1.Ok ∧ p.1.2.1 + 1 + p.1.2.2 = p.1.1.w ∧ 2 ≤ p.1.1.w ∧ p.2 ∈ [2, 3])
    (hcmp : (t0.1.1.nextPass t0.2).O = 3 → ∃ z, 1 ≤ (t0.1.1.nextPass t0.2).k ∧
      (t0.1.1.nextPass t0.2).E = fld ((t0.1.1.nextPass t0.2).k + z) (t0.1.1.nextPass t0.2).k) :
    znttLogic.Reach
      (hd QNTT.FAL (Pm ++ [1, 1] ++ (t0.1.1.doneX t0.1.2.1 t0.1.2.2 t0.2).ps.body ++
        tailP (ts.map fun p => p.1.1.doneX p.1.2.1 p.1.2.2 p.2)) [])
      (hd QNTT.RFL (curTapeG Pm [] (t0.1.1.nextPass t0.2).curG 0 ((t0.1.1.nextPass t0.2).k - 1)
        ((t0.1.1.nextPass t0.2).w - (t0.1.1.nextPass t0.2).k)
        ((ts.map fun p => p.1.1.nextPass p.2).map VR.dec)) []) := by
  have h0 := h t0 (by simp)
  have hws : ∀ x ∈ ts.map (fun p => p.1.1.nextPass p.2), x.Ok := by
    intro x hx; simp only [List.mem_map] at hx; obtain ⟨p, hp, rfl⟩ := hx
    have := h p (by simp [hp]); exact VR.nextPass_ok _ this.1 _ this.2.2.2 this.2.2.1
  have hw := VR.nextPass_ok _ h0.1 _ h0.2.2.2 h0.2.2.1
  have e1 := done_ps_vr t0.1.1 h0.1 t0.1.2.1 t0.1.2.2 t0.2 h0.2.1 h0.2.2.1 h0.2.2.2
  have e2 := tailVR_doneX ts (fun p hp => h p (by simp [hp]))
  have hLe : Pm ++ 1 :: 1 :: ([(t0.1.1.nextPass t0.2).F, (t0.1.1.nextPass t0.2).O, (t0.1.1.nextPass t0.2).P] ++
      1 :: ((t0.1.1.nextPass t0.2).tl ++ tailVR (ts.map fun p => p.1.1.nextPass p.2))) =
      Pm ++ [1, 1] ++ (t0.1.1.doneX t0.1.2.1 t0.1.2.2 t0.2).ps.body ++
        tailP (ts.map fun p => p.1.1.doneX p.1.2.1 p.1.2.2 p.2) := by
    rw [e2]
    have := congrArg (fun l => Pm ++ l ++ tailVR (ts.map fun p => p.1.1.nextPass p.2)) e1
    simp only [VR.recd, List.append_assoc, List.cons_append, List.nil_append] at this ⊢
    simpa using this.symm
  have hL : NoB (Pm ++ 1 :: 1 :: ([(t0.1.1.nextPass t0.2).F, (t0.1.1.nextPass t0.2).O, (t0.1.1.nextPass t0.2).P] ++
      1 :: ((t0.1.1.nextPass t0.2).tl ++ tailVR (ts.map fun p => p.1.1.nextPass p.2)))) := by
    have := NoB_app_iff.2 ⟨hP.noB, NoB_app_iff.2 ⟨hw.recd_noB, tailVR_noB _ hws⟩⟩
    simpa [VR.recd, List.append_assoc] using this
  rw [← hLe]
  exact faG' _ Pm hL hP _ hw _ hws hcmp rfl


def retagPf (r : Rc) (x : Nat) : Rc := { r with Pf := x }

theorem retag_self : ∀ post : List Rc, List.zipWith retagPf post (post.map Rc.Pf) = post
  | [] => rfl
  | x :: xs => by simp [List.zipWith, retagPf, retag_self xs]

theorem retagMove : ∀ (pre0 : List Rc) (j : Nat), pre0.map Rc.Pf = List.replicate j 2 →
    ∀ (r r2 : Rc) (post : List Rc) (l' : List Nat), post.map Rc.Pf = l' →
    List.zipWith retagPf (pre0 ++ r :: r2 :: post) (List.replicate (j + 1) 2 ++ 3 :: l') =
      pre0 ++ { r with Pf := 2 } :: { r2 with Pf := 3 } :: post
  | [], j, h, r, r2, post, l', hp => by
    have : j = 0 := by have := congrArg List.length h; simpa using this.symm
    subst this
    simp [List.zipWith, retagPf, ← hp, retag_self]
  | x :: xs, j, h, r, r2, post, l', hp => by
    cases j with
    | zero => simp at h
    | succ j =>
      simp only [List.map_cons, List.replicate_succ, List.cons.injEq] at h
      obtain ⟨hx, hxs⟩ := h
      have ih := retagMove xs j (by simpa [List.replicate_succ] using hxs) r r2 post l' hp
      simp only [List.replicate_succ, List.cons_append, List.zipWith_cons_cons, List.cons_append] at ih ⊢
      rw [ih]
      have hx' : ({ x with Pf := 2 } : Rc) = x := by
        rcases x with ⟨F, O, Pf, acc, E, b0, br, u0, ur⟩
        simp at hx; subst hx; rfl
      simp [retagPf, hx']

theorem doneX_zip : ∀ (cs : List (VR × Nat × Nat)) (xs : List Nat), cs.length = xs.length →
    ((cs.zip xs).map fun p => p.1.1.doneX p.1.2.1 p.1.2.2 p.2) =
      List.zipWith retagPf (cs.map fun t => t.1.done t.2.1 t.2.2) xs
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | c :: cs, x :: xs, h => by
    have ih := doneX_zip cs xs (by simpa using h)
    simp only [List.zip_cons_cons, List.map_cons, List.zipWith_cons_cons]
    rw [ih]
    simp [retagPf, VR.doneX, VR.done, VR.toRcA]


theorem flags_split : ∀ (pre0 : List Rc), (∀ x ∈ pre0, x.Pf = 2) → ∀ (j : Nat) (rest rest' : List Nat),
    pre0.map Rc.Pf ++ 3 :: rest = List.replicate j 2 ++ 3 :: rest' →
    pre0.map Rc.Pf = List.replicate j 2 ∧ rest = rest'
  | [], _, j, rest, rest', h => by
    cases j with
    | zero => simp at h; exact ⟨rfl, h⟩
    | succ j => simp [List.replicate_succ] at h
  | x :: xs, hx, j, rest, rest', h => by
    cases j with
    | zero => have := hx x (by simp); simp at h; omega
    | succ j =>
      simp only [List.map_cons, List.cons_append, List.replicate_succ, List.cons.injEq] at h
      have ih := flags_split xs (fun y hy => hx y (by simp [hy])) j rest rest' h.2
      refine ⟨?_, ih.2⟩
      simp [List.replicate_succ, ih.1, hx x (by simp)]

theorem VR.done_ps (c : VR) (hc : c.Ok) (r s : Nat) (hrs : r + 1 + s = c.w) (hw2 : 2 ≤ c.w) : (c.done r s).PS :=
  { ok := c.done_ok hc r s,
    acc2 := by simp [VR.done, VR.toRcA]; omega,
    rest := by
      have := VR.toRcA_rest c (List.replicate r 2 ++ 3 :: List.replicate s 2)
      simpa [VR.done, VR.toRcA, Rc.Rest] using this }

/-- `SC` after a non-final pass with `S = 0`, from the finished (`done`) records: the next pass starts at `FAL`
on the records with the moved input flags. -/
theorem scChain (Wf : List Nat) (hW : BitsD Wf) (Q : List Nat) (a b q : Nat)
    (hP2 : GoodW (1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
    (cs : List (VR × Nat × Nat)) (hcs : ∀ t ∈ cs, t.1.Ok ∧ t.2.1 + 1 + t.2.2 = t.1.w ∧ 2 ≤ t.1.w)
    (j : Nat) (y : Nat) (l' : List Nat)
    (hfl : cs.map (fun t => t.1.P) = List.replicate j 2 ++ 3 :: y :: l') (hq : 1 ≤ q) :
    ∃ t0 ts, (cs.zip (List.replicate (j + 1) 2 ++ 3 :: l')) = t0 :: ts ∧
      znttLogic.Reach
        (hd QNTT.SC (Wf ++ 1 :: (List.replicate q 3 ++ 1 :: Q) ++ List.replicate a 3)
          (3 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2))))
        (hd QNTT.FAL ((Wf ++ 1 :: (List.replicate q 3 ++ 1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2))) ++
          [1, 1] ++ (t0.1.1.doneX t0.1.2.1 t0.1.2.2 t0.2).ps.body ++
            tailP (ts.map fun p => p.1.1.doneX p.1.2.1 p.1.2.2 p.2)) []) := by
  have hlen : cs.length = (List.replicate (j + 1) 2 ++ 3 :: l').length := by
    have := congrArg List.length hfl
    simp at this ⊢; omega
  obtain ⟨pre0, r, r2, post, r0, rs, he, hp0, hp3, hr0, h⟩ := scStart Wf hW Q a b q hP2
    (cs.map fun t => t.1.done t.2.1 t.2.2)
    (fun x hx => by
      simp only [List.mem_map] at hx; obtain ⟨t, ht, rfl⟩ := hx
      exact VR.done_ps _ (hcs t ht).1 _ _ (hcs t ht).2.1 (hcs t ht).2.2)
    j (y :: l') (by simpa [VR.done, VR.toRcA, Function.comp_def] using hfl) (by simp) hq
  have hfl' : pre0.map Rc.Pf ++ 3 :: r2.Pf :: post.map Rc.Pf = List.replicate j 2 ++ 3 :: y :: l' := by
    have := congrArg (List.map Rc.Pf) he
    rw [← hfl]
    simpa [VR.done, VR.toRcA, hp3, Function.comp_def] using this.symm
  obtain ⟨hP0, hrest⟩ := flags_split pre0 hp0 j _ _ hfl'
  have hPost : post.map Rc.Pf = l' := (by simpa using hrest : r2.Pf = y ∧ post.map Rc.Pf = l').2
  have hmove := retagMove pre0 j hP0 r r2 post l' hPost
  rw [← he, ← doneX_zip cs _ hlen] at hmove
  rw [hr0] at hmove
  obtain ⟨t0, ts, hz⟩ : ∃ t0 ts, cs.zip (List.replicate (j + 1) 2 ++ 3 :: l') = t0 :: ts := by
    cases hz : cs.zip (List.replicate (j + 1) 2 ++ 3 :: l') with
    | nil => rw [hz] at hmove; simp at hmove
    | cons t ts => exact ⟨t, ts, rfl⟩
  refine ⟨t0, ts, hz, ?_⟩
  rw [hz] at hmove
  simp only [List.map_cons, List.cons.injEq] at hmove
  obtain ⟨h1, h2⟩ := hmove
  rw [h1, h2]
  exact h


/-- One non-final pass from its start (no finished records yet): it either refutes (`S ≠ 0`, state `ODL`) or leads to the
start of the next pass (`FAL`, records `doneX` with the moved input flag). -/
theorem passCycle (Wf : List Nat) (hW : BitsD Wf) (Q : List Nat) (a b : Nat)
    (hP2 : GoodW (1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
    (n : Nat) (vs : List VR) (c : VR) (p : Nat × Nat) (r s : Nat)
    (hrs : r + 1 + s = c.w) (hlen : vs.length = n) (hc : CurInv c) (hvs : ∀ x ∈ vs, x.Ok) (hom : OutM vs)
    (hp : 1 ≤ p.2) (hcmp : PassCmp n r vs) (hcw : 2 ≤ c.w) (hvw : ∀ x ∈ vs, 2 ≤ x.w)
    (j y : Nat) (l' : List Nat) (hfl : c.P :: vs.map VR.P = List.replicate j 2 ++ 3 :: y :: l') :
    ∃ (p' : Nat × Nat) (cs : List (VR × Nat × Nat)), 1 ≤ p'.2 ∧ (∀ t ∈ cs, t.1.Ok ∧ t.2.1 + 1 + t.2.2 = t.1.w ∧ 2 ≤ t.1.w) ∧
      cs.map (fun t => t.1.P) = c.P :: vs.map VR.P ∧
      (∃ lo : LoopOut, loopRun n c vs r s p = lo ∧ cs = lo.cs ++ [(outRec lo.c' lo.r', lo.r', lo.s')] ∧
        p' = outP lo.c' lo.r' lo.p') ∧
      ((p'.1 = 0 ∧ ∃ t0 ts, cs.zip (List.replicate (j + 1) 2 ++ 3 :: l') = t0 :: ts ∧
        znttLogic.Reach
          (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
            [] c 0 r s vs) [])
          (hd QNTT.FAL ((Wf ++ 1 :: (List.replicate p'.2 3 ++ 1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2))) ++
            [1, 1] ++ (t0.1.1.doneX t0.1.2.1 t0.1.2.2 t0.2).ps.body ++
              tailP (ts.map fun p => p.1.1.doneX p.1.2.1 p.1.2.2 p.2)) [])) ∨
       (∃ k, p'.1 = k + 1 ∧
        znttLogic.Reach
          (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
            [] c 0 r s vs) [])
          (hd QNTT.ODL (Wf ++ [1]) (2 :: (List.replicate k 2 ++ List.replicate p'.2 3 ++
            1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2)))))))) := by
  obtain ⟨p', pre', cs, hpre', hne, hp', hpe, hcs, hPc, hLo, h1⟩ :=
    passMore2 Wf hW Q a b hP2 n vs c [] p r s hrs hlen hc hvs hom (by intro x hx; simp at hx) hp hcmp hcw hvw
  simp only [List.nil_append] at hpe
  subst hpe
  refine ⟨p', cs, hp', hcs, hPc, hLo, ?_⟩
  rcases hk : p'.1 with _ | k
  · left
    refine ⟨rfl, ?_⟩
    have hfl' : cs.map (fun t => t.1.P) = List.replicate j 2 ++ 3 :: y :: l' := by rw [hPc]; exact hfl
    obtain ⟨t0, ts, hz, h2⟩ := scChain Wf hW Q a b p'.2 hP2 cs (fun t ht => hcs t ht) j y l' hfl' hp'
    refine ⟨t0, ts, hz, ?_⟩
    rw [hk] at h1
    simp only [List.replicate_zero, List.nil_append] at h1
    exact h1.trans h2
  · right
    refine ⟨k, rfl, ?_⟩
    rw [hk] at h1
    have nP := hP2.noB
    simp only [NoB_cons_iff, NoB_app_iff] at nP
    have n1 : (1 : Nat) ∈ NB := by simp [NB]
    have n3 : (3 : Nat) ∈ NB := by simp [NB]
    have hQ : Sym4 Q := by
      have := hP2.sym4
      simp only [Sym4_cons_iff, Sym4_app_iff] at this
      exact this.2.1.1
    have nQ : NoB Q := nP.2.1.1
    have s3 : ∀ j, Sym4 (List.replicate j 3) := fun j => (BitsD.rep j 3 (by simp)).sym4
    have s2 : ∀ j, Sym4 (List.replicate j 2) := fun j => (BitsD.rep j 2 (by simp)).sym4
    have sT : Sym4 (tailB (cs.map fun t => t.1.done t.2.1 t.2.2)) := tailB_sym4 _ (fun x hx => (hpre' x hx).1)
    have hX : NoB (Wf ++ 1 :: (List.replicate (k + 1) 2 ++ List.replicate p'.2 3 ++ 1 :: Q) ++ List.replicate a 3) := by
      have n2 : (2 : Nat) ∈ NB := by simp [NB]
      simp only [NoB_cons_iff, NoB_app_iff]
      exact ⟨⟨hW.noB, n1, ⟨noB_rep _ 2 (by simp), noB_rep _ 3 (by simp)⟩, n1, nQ⟩, noB_rep a 3 (by simp)⟩
    have hY : Sym4 (3 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2))) :=
      Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) ((s2 b).app sT))
    have hT : Sym4 (1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2)))) :=
      Sym4.cons (by simp [ALL]) ((hQ.app (s3 a)).app hY)
    have h2 := scFail Wf hW (List.replicate k 2 ++ List.replicate p'.2 3)
      (1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2))))
      (Wf ++ 1 :: (List.replicate (k + 1) 2 ++ List.replicate p'.2 3 ++ 1 :: Q) ++ List.replicate a 3)
      (3 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2)))
      (bd_app (BitsD.rep k 2 (by simp)) (BitsD.rep _ 3 (by simp))) hT
      (by simp [List.replicate_succ, List.append_assoc]) hX hY
    simp only [List.replicate_succ, List.cons_append, List.append_assoc] at h1 h2 ⊢
    exact h1.trans h2


/-- The last pass from its start: `S ≠ 0` succeeds (`SU1`), `S = 0` refutes (`ODL`). -/
theorem lastCycle (Wf : List Nat) (hW : BitsD Wf) (Q : List Nat) (b : Nat)
    (hP2 : GoodW (1 :: (Q ++ [1] ++ [3] ++ List.replicate b 2)))
    (n : Nat) (vs : List VR) (c : VR) (p : Nat × Nat) (r s : Nat)
    (hrs : r + 1 + s = c.w) (hlen : vs.length = n) (hc : CurInv c) (hvs : ∀ x ∈ vs, x.Ok) (hom : OutM vs)
    (hp : 1 ≤ p.2) (hcmp : PassCmp n r vs) (hcw : 2 ≤ c.w) (hvw : ∀ x ∈ vs, 2 ≤ x.w) :
    ∃ (p' : Nat × Nat) (cs : List (VR × Nat × Nat)), 1 ≤ p'.2 ∧ (∀ t ∈ cs, t.1.Ok ∧ t.2.1 + 1 + t.2.2 = t.1.w ∧ 2 ≤ t.1.w) ∧
      cs.map (fun t => t.1.P) = c.P :: vs.map VR.P ∧
      (∃ lo : LoopOut, loopRun n c vs r s p = lo ∧ cs = lo.cs ++ [(outRec lo.c' lo.r', lo.r', lo.s')] ∧
        p' = outP lo.c' lo.r' lo.p') ∧
      ((∃ k, p'.1 = k + 1 ∧
        znttLogic.Reach
          (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: (Q ++ [1] ++ [3] ++ List.replicate b 2)))
            [] c 0 r s vs) [])
          (hdR QNTT.SU1 [] (Wf ++ 1 :: (List.replicate (k + 1) 2 ++ List.replicate p'.2 3 ++
            1 :: (Q ++ 1 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2))))))) ∨
       (p'.1 = 0 ∧
        znttLogic.Reach
          (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: (Q ++ [1] ++ [3] ++ List.replicate b 2)))
            [] c 0 r s vs) [])
          (hd QNTT.ODL (Wf ++ [1]) (List.replicate p'.2 3 ++
            1 :: (Q ++ 1 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2))))))) := by
  obtain ⟨p', pre', cs, hpre', hne, hp', hpe, hcs, hPc, hLo, h1⟩ :=
    passLast2 Wf hW Q b hP2 n vs c [] p r s hrs hlen hc hvs hom (by intro x hx; simp at hx) hp hcmp hcw hvw
  simp only [List.nil_append] at hpe
  subst hpe
  refine ⟨p', cs, hp', hcs, hPc, hLo, ?_⟩
  have n1 : (1 : Nat) ∈ NB := by simp [NB]
  have n2 : (2 : Nat) ∈ NB := by simp [NB]
  have n3 : (3 : Nat) ∈ NB := by simp [NB]
  have nQ : NoB Q := fun x hx => hP2.noB x (by simp [hx])
  have hQ : Sym4 Q := nQ.sym4
  have s2 : ∀ j, Sym4 (List.replicate j 2) := fun j => (BitsD.rep j 2 (by simp)).sym4
  have sT : Sym4 (tailB (cs.map fun t => t.1.done t.2.1 t.2.2)) := tailB_sym4 _ (fun x hx => (hpre' x hx).1)
  have nT : NoB (tailB (cs.map fun t => t.1.done t.2.1 t.2.2)) := tailB_noB _ (fun x hx => (hpre' x hx).1)
  have hY : Sym4 (1 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2))) :=
    Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) ((s2 b).app sT))
  have hTn : NoB (1 :: (Q ++ 1 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2)))) := by
    simp only [NoB_cons_iff, NoB_app_iff]
    exact ⟨n1, nQ, n1, n2, noB_rep b 2 (by simp), nT⟩
  have hT : Sym4 (1 :: (Q ++ 1 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2)))) :=
    Sym4.cons (by simp [ALL]) (hQ.app hY)
  have hX0 : ∀ S : List Nat, NoB S → NoB (Wf ++ 1 :: (S ++ 1 :: Q)) := fun S hS => by
    simp only [NoB_cons_iff, NoB_app_iff]; exact ⟨hW.noB, n1, hS, n1, nQ⟩
  have sR : ∀ S : List Nat, Sym4 S → Sym4 (S ++ 1 :: (Q ++ 1 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2)))) :=
    fun S hS => hS.app hT
  rcases hk : p'.1 with _ | k
  · right
    refine ⟨rfl, ?_⟩
    rw [hk] at h1
    simp only [List.replicate_zero, List.nil_append] at h1
    have hX := hX0 (List.replicate p'.2 3) (noB_rep _ 3 (by simp))
    obtain ⟨q, hq⟩ : ∃ q, p'.2 = q + 1 := ⟨p'.2 - 1, by omega⟩
    have h0 := fl0Scan (Wf ++ 1 :: (List.replicate p'.2 3 ++ 1 :: Q))
      (1 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2))) hX hY
    have sR3 : Sym4 (List.replicate q 3 ++ 1 :: (Q ++ 1 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2)))) :=
      (BitsD.rep q 3 (by simp)).sym4.app hT
    have b1 := fl1Block [] Wf (1 :: 3 :: (List.replicate q 3 ++ 1 :: (Q ++ 1 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2)))))
      Sym4.nil hW (Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) sR3))
    have b2 := fl1M ([] ++ Wf) (3 :: (List.replicate q 3 ++ 1 :: (Q ++ 1 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2)))))
      (by simpa using hW.sym4) (Sym4.cons (by simp [ALL]) sR3)
    have b3 := fl2One ([] ++ Wf ++ [1]) (List.replicate q 3 ++ 1 :: (Q ++ 1 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2))))
      (by simpa using hW.sym4.app (Sym4.cons (by simp [ALL]) Sym4.nil)) sR3
    rw [hq] at h1 h0 ⊢
    simp only [List.replicate_succ, List.cons_append, List.append_assoc, List.nil_append] at h0 b1 b2 b3 h1 ⊢
    exact h1.trans (h0.trans (b1.trans (b2.trans b3)))
  · left
    refine ⟨k, rfl, ?_⟩
    rw [hk] at h1
    have hSn : NoB (List.replicate (k + 1) 2 ++ List.replicate p'.2 3) :=
      NoB_app_iff.2 ⟨noB_rep _ 2 (by simp), noB_rep _ 3 (by simp)⟩
    have h2 := flOk Wf hW (List.replicate (k + 1) 2 ++ List.replicate p'.2 3)
      (1 :: (Q ++ 1 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2))))
      (Wf ++ 1 :: (List.replicate (k + 1) 2 ++ List.replicate p'.2 3 ++ 1 :: Q))
      (1 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2)))
      (bd_app (BitsD.rep _ 2 (by simp)) (BitsD.rep _ 3 (by simp))) hT 0
      ⟨List.replicate k 2 ++ List.replicate p'.2 3, by simp [List.replicate_succ]⟩
      (by simp) (hX0 _ hSn) hY hTn
    simp only [List.append_assoc, List.cons_append] at h1 h2 ⊢
    exact h1.trans h2


theorem outRec_m (c : VR) (r : Nat) : (outRec c r).m = c.m ∧ (outRec c r).O = c.O := by
  unfold outRec; split <;> simp

theorem loopRun_m : ∀ (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat),
    CurInv c → (∀ x ∈ vs, x.Ok) → OutM vs → vs.length = n →
    (∀ t ∈ (loopRun n c vs r s p).cs, t.1.O = 3 → t.1.m = 0) ∧
    ((loopRun n c vs r s p).c'.O = 3 → (loopRun n c vs r s p).c'.m = 0) := by
  intro n
  induction n with
  | zero =>
    intro c vs r s p hc hvs hom hl
    simp [loopRun, hc.2.2]
    exact fun h => (hc.2.2 h).1
  | succ n ih =>
    intro c vs r s p hc hvs hom hl
    have hlen' := stepN_length r vs
    obtain ⟨w, ws, hw⟩ : ∃ w ws, stepN r vs = w :: ws := by
      cases h : stepN r vs with
      | nil => rw [h] at hlen'; simp at hlen'; omega
      | cons w ws => exact ⟨w, ws, rfl⟩
    have hok := stepN_ok r vs hvs
    rw [hw] at hok
    have hwOk : w.Ok := hok w (by simp)
    have hout := stepN_outM r vs hom
    rw [hw] at hout
    have hwm : w.O = 3 → w.m = 0 := hout w (by simp)
    have hwsOk' : ∀ x ∈ ws.map VR.dec, x.Ok := by
      intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
      exact y.dec_ok (hok y (by simp [hy]))
    have homws : OutM (ws.map VR.dec) := dec_outM ws (fun x hx => hout x (by simp [hx]))
    have hlenws : (ws.map VR.dec).length = n := by
      rw [hw] at hlen'; simp at hlen'; simp; omega
    have ih' := ih w.curG (ws.map VR.dec) (w.k - 1) (w.w - w.k) (outP c r p) (curG_inv w hwOk hwm) hwsOk' homws hlenws
    simp only [loopRun, hw]
    refine ⟨?_, ih'.2⟩
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · intro h3
      rw [(outRec_m c r).2] at h3
      rw [(outRec_m c r).1]
      exact (hc.2.2 h3).1
    · exact ih'.1 t ht


def nxtW (t0 : (VR × Nat × Nat) × Nat) : VR := t0.1.1.nextPass t0.2
def nxtC (t0 : (VR × Nat × Nat) × Nat) : VR := (nxtW t0).curG
def nxtVs (ts : List ((VR × Nat × Nat) × Nat)) : List VR := (ts.map fun q => q.1.1.nextPass q.2).map VR.dec
def nxtR (t0 : (VR × Nat × Nat) × Nat) : Nat := (nxtW t0).k - 1
def nxtS (t0 : (VR × Nat × Nat) × Nat) : Nat := (nxtW t0).w - (nxtW t0).k

theorem goodW_pmNext (Wf : List Nat) (hW : BitsD Wf) (Q : List Nat) (a b q : Nat)
    (hP2 : GoodW (1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2))) (hq : 1 ≤ q) :
    GoodW (Wf ++ 1 :: (List.replicate q 3 ++ 1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2))) := by
  have hG : GoodW (1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2)) := by
    have := goodW_swap_tail (1 :: (Q ++ List.replicate a 3)).length (1 :: (Q ++ List.replicate a 3)) 3 3
      (3 :: List.replicate b 2) (2 :: List.replicate b 2) rfl (by simp) (by simp)
      (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all)
      (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all)
      (by
        have e : (1 :: (Q ++ List.replicate a 3)) ++ 3 :: 3 :: List.replicate b 2 =
            1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2) := by
          simp only [List.replicate_succ, List.cons_append, List.append_assoc, List.nil_append]
          have key : ∀ (a : Nat) (L : List Nat), List.replicate a 3 ++ 3 :: L = 3 :: (List.replicate a 3 ++ L) := by
            intro a L; induction a with
            | zero => simp
            | succ a ih => simp [List.replicate_succ, ih]
          rw [key, key]
        rw [e]; exact hP2)
    simpa [List.append_assoc] using this
  exact goodW_reg Wf (List.replicate q 3) _ hW (BitsD.rep q 3 (by simp))
    (by intro h; have := congrArg List.length h; simp at this; omega) hG

theorem vis_m0 (v : VR) (h : v.m = 0) : v.vis.m = 0 := by unfold VR.vis; split <;> simp [h]
theorem inc_m0 (v : VR) (h : v.m = 0) : v.inc.m = 0 := by simpa [VR.inc] using h
theorem dec_m0 (v : VR) (h : v.m = 0) : v.dec.m = 0 := by unfold VR.dec; split <;> simp [h]
theorem curG_m0 (v : VR) (h : v.m = 0) : v.curG.m = 0 := by
  unfold VR.curG VR.cur VR.dec; split <;> split <;> simp [h]

theorem stepList_m0 : ∀ vs : List VR, (∀ v ∈ vs, v.m = 0) → ∀ w ∈ stepList vs, w.m = 0
  | [], _ => by simp [stepList]
  | v :: vs, h => by
    intro w hw
    simp only [stepList, List.mem_cons, List.mem_map] at hw
    rcases hw with rfl | ⟨x, hx, rfl⟩
    · exact vis_m0 _ (inc_m0 _ (h v (by simp)))
    · exact vis_m0 _ (h x (by simp [hx]))

theorem stepN_m0 (r : Nat) : ∀ (vs : List VR), (∀ v ∈ vs, v.m = 0) → ∀ w ∈ stepN r vs, w.m = 0 := by
  induction r with
  | zero => intro vs h; simpa [stepN] using h
  | succ r ih => intro vs h; exact ih _ (stepList_m0 vs h)

theorem nextPass_m (c : VR) (x : Nat) : (c.nextPass x).m = c.m := rfl

theorem loopRun_m0 : ∀ (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat),
    c.m = 0 → (∀ x ∈ vs, x.m = 0) → vs.length = n →
    (∀ t ∈ (loopRun n c vs r s p).cs, t.1.m = 0) ∧ (loopRun n c vs r s p).c'.m = 0 := by
  intro n
  induction n with
  | zero => intro c vs r s p hc hvs hl; simp [loopRun, hc]
  | succ n ih =>
    intro c vs r s p hc hvs hl
    have hlen' := stepN_length r vs
    obtain ⟨w, ws, hw⟩ : ∃ w ws, stepN r vs = w :: ws := by
      cases h : stepN r vs with
      | nil => rw [h] at hlen'; simp at hlen'; omega
      | cons w ws => exact ⟨w, ws, rfl⟩
    have hmz := stepN_m0 r vs hvs
    rw [hw] at hmz
    have hlenws : (ws.map VR.dec).length = n := by
      rw [hw] at hlen'; simp at hlen'; simp; omega
    have ih' := ih w.curG (ws.map VR.dec) (w.k - 1) (w.w - w.k) (outP c r p)
      (curG_m0 _ (hmz w (by simp)))
      (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx; exact dec_m0 _ (hmz y (by simp [hy])))
      hlenws
    simp only [loopRun, hw]
    refine ⟨?_, ih'.2⟩
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · rw [(outRec_m c r).1]; exact hc
    · exact ih'.1 t ht


/-- A finished record as an odometer record. -/
def VR.toO (t : VR) (r s : Nat) : ORec :=
  { F := 2, O := t.O, Pf := t.P, acc := List.replicate r 2 ++ 3 :: List.replicate s 2, E := t.E,
    d := t.n, r := t.n + 1 + t.s, z := t.a, k := t.c + 1, m := t.t }

theorem VR.done_body_toO (t : VR) (ht : t.Ok) (hm : t.m = 0) (r s : Nat) :
    (t.done r s).body = (t.toO r s).tape := by
  have h1 := t.toRcA_tl ht (List.replicate r 2 ++ 3 :: List.replicate s 2)
  have h2 : (t.done r s).tl = (t.toRcA (List.replicate r 2 ++ 3 :: List.replicate s 2)).tl := rfl
  rw [Rc.body_eq, h2, h1]
  simp only [VR.done, VR.toRcA, ORec.tape, VR.toO]
  have hb : t.b = therm t.n (t.n + 1 + t.s) := by
    simp [VR.b, therm, hm]
  have hu : t.u = winStr t.a (t.c + 1) t.t := by simp [VR.u, winStr]
  rw [hb, hu]

theorem tailB_toO : ∀ (cs : List (VR × Nat × Nat)), (∀ t ∈ cs, t.1.Ok ∧ t.1.m = 0) →
    tailB (cs.map fun t => t.1.done t.2.1 t.2.2) = sepRest (cs.map fun t => t.1.toO t.2.1 t.2.2)
  | [], _ => by simp [tailB, sepRest]
  | t :: cs, h => by
    have ih := tailB_toO cs (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, tailB, sepRest, ih]
    rw [VR.done_body_toO _ (h t (by simp)).1 (h t (by simp)).2]

theorem toO_ok (t : VR) (ht : t.Ok) (r s : Nat) (hrs : r + 1 + s = t.w) : (t.toO r s).Ok :=
  { hF := by
      have h1 := ht.O; have h2 := ht.P
      simp at h1 h2
      simp [VR.toO]; omega,
    acc := bd_app (BitsD.rep _ _ (by simp)) (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all),
    E := ht.E, d := by simp [VR.toO], k := by simp [VR.toO], Elen := by simpa [VR.toO] using ht.Elen,
    Elw := by simp [VR.toO]; have := ht.Elw; omega }


def passCsOf (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat) : List (VR × Nat × Nat) :=
  (loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
    (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]

def passQOf (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat) : Nat :=
  (outP (loopRun n c vs r s p).c' (loopRun n c vs r s p).r' (loopRun n c vs r s p).p').2

/-- Tails of the tape for `m` further passes. -/
def NnTail (m b : Nat) : List Nat := List.replicate (m + 1) 3 ++ List.replicate b 2

/-- Shape of a refuted configuration: a good prefix and the finished records. -/
def OdlOut (L R : List Nat) : Prop :=
  ∃ (u : List Nat) (pre' : List Rc), GoodW u ∧ (∀ x ∈ pre', x.Ok) ∧ pre' ≠ [] ∧ L ++ R = u ++ tailB pre'

theorem goodW_shiftNn (Q : List Nat) (a b : Nat)
    (hP2 : GoodW (1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2))) :
    GoodW (1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2)) := by
  have := goodW_swap_tail (1 :: (Q ++ List.replicate a 3)).length (1 :: (Q ++ List.replicate a 3)) 3 3
    (3 :: List.replicate b 2) (2 :: List.replicate b 2) rfl (by simp) (by simp)
    (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all)
    (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all)
    (by
      have e : (1 :: (Q ++ List.replicate a 3)) ++ 3 :: 3 :: List.replicate b 2 =
          1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2) := by
        simp only [List.replicate_succ, List.cons_append, List.append_assoc, List.nil_append]
        have key : ∀ (a : Nat) (L : List Nat), List.replicate a 3 ++ 3 :: L = 3 :: (List.replicate a 3 ++ L) := by
          intro a L; induction a with
          | zero => simp
          | succ a ih => simp [List.replicate_succ, ih]
        rw [key, key]
      rw [e]; exact hP2)
  simpa [List.append_assoc] using this


/-- Digit signature: the odometer-relevant numbers `(d, e, z, m, (w, O))`. -/
abbrev DG := Nat × Nat × Nat × Nat × (Nat × Nat)

/-- The digit data of a record, invariant under the pass machinery. -/
def VR.dg (v : VR) : DG := (v.n, v.s, v.a + v.c, v.t, (v.w, v.O))

theorem dg_inc (v : VR) : v.inc.dg = v.dg ∧ v.inc.m = v.m := ⟨rfl, rfl⟩

theorem dg_vis (v : VR) (h : v.m = 0) : v.vis.dg = v.dg ∧ v.vis.m = 0 := by
  unfold VR.vis; split <;> simp [VR.dg, h, *]

theorem dg_dec (v : VR) : v.dec.dg = v.dg ∧ v.dec.m = v.m := by
  unfold VR.dec; split
  · simp
  · simp [VR.dg]; omega

theorem dg_curG (v : VR) : v.curG.dg = v.dg ∧ v.curG.m = v.m := by
  have h : v.cur.dg = v.dg ∧ v.cur.m = v.m := by
    unfold VR.cur; simpa [VR.dg] using dg_dec v
  unfold VR.curG; split
  · simpa [VR.dg] using h
  · exact h

theorem dg_stepN : ∀ (r : Nat) (vs : List VR), (∀ x ∈ vs, x.m = 0) →
    ∀ w ∈ stepN r vs, (∃ x ∈ vs, w.dg = x.dg) ∧ w.m = 0 := by
  intro r
  induction r with
  | zero => intro vs h w hw; exact ⟨⟨w, hw, rfl⟩, h w hw⟩
  | succ r ih =>
    intro vs h w hw
    have h1 : ∀ x ∈ stepList vs, (∃ y ∈ vs, x.dg = y.dg) ∧ x.m = 0 := by
      intro x hx
      unfold stepList at hx
      cases vs with
      | nil => simp at hx
      | cons v vs' =>
        simp only [List.mem_cons, List.mem_map] at hx
        rcases hx with rfl | ⟨y, hy, rfl⟩
        · have := dg_vis v.inc (by show v.m = 0; exact h v (by simp))
          exact ⟨⟨v, by simp, by rw [this.1]; rfl⟩, this.2⟩
        · have := dg_vis y (h y (by simp [hy]))
          exact ⟨⟨y, by simp [hy], this.1⟩, this.2⟩
    have := ih (stepList vs) (fun x hx => (h1 x hx).2) w hw
    obtain ⟨⟨x, hx, e⟩, hm⟩ := this
    exact ⟨⟨(h1 x hx).1.choose, (h1 x hx).1.choose_spec.1, by rw [e]; exact (h1 x hx).1.choose_spec.2⟩, hm⟩

theorem dg_loopRun : ∀ (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat),
    c.m = 0 → (∀ x ∈ vs, x.m = 0) →
    ∀ t ∈ (loopRun n c vs r s p).cs, ∃ x ∈ c :: vs, t.1.dg = x.dg := by
  intro n
  induction n with
  | zero => intro c vs r s p _ _ t ht; simp [loopRun] at ht
  | succ n ih =>
    intro c vs r s p hc hvs t ht
    unfold loopRun at ht
    split at ht
    · simp at ht
    · rename_i w ws hw
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact ⟨c, by simp, by unfold outRec; split <;> simp [VR.dg]⟩
      · have hall : ∀ x ∈ w :: ws, (∃ y ∈ vs, x.dg = y.dg) ∧ x.m = 0 := by
          intro x hx; rw [← hw] at hx; exact dg_stepN r vs hvs x hx
        have hwm := (hall w (by simp)).2
        have := ih w.curG (ws.map VR.dec) (w.k - 1) (w.w - w.k) (outP c r p)
          (by rw [(dg_curG w).2]; exact hwm)
          (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
              rw [(dg_dec y).2]; exact (hall y (by simp [hy])).2) t ht
        obtain ⟨x, hx, e⟩ := this
        simp only [List.mem_cons, List.mem_map] at hx
        rcases hx with rfl | ⟨y, hy, rfl⟩
        · obtain ⟨⟨z, hz, e2⟩, _⟩ := hall w (by simp)
          exact ⟨z, by simp [hz], by rw [e, (dg_curG w).1, e2]⟩
        · obtain ⟨⟨z, hz, e2⟩, _⟩ := hall y (by simp [hy])
          exact ⟨z, by simp [hz], by rw [e, (dg_dec y).1, e2]⟩

theorem dg_loopRun_c : ∀ (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat),
    c.m = 0 → (∀ x ∈ vs, x.m = 0) →
    ∃ x ∈ c :: vs, (loopRun n c vs r s p).c'.dg = x.dg ∧ (loopRun n c vs r s p).c'.m = 0 := by
  intro n
  induction n with
  | zero => intro c vs r s p hc hvs; exact ⟨c, by simp, by simp [loopRun], by simp [loopRun, hc]⟩
  | succ n ih =>
    intro c vs r s p hc hvs
    unfold loopRun
    split
    · exact ⟨c, by simp, rfl, hc⟩
    · rename_i w ws hw
      have hall : ∀ x ∈ w :: ws, (∃ y ∈ vs, x.dg = y.dg) ∧ x.m = 0 := by
        intro x hx; rw [← hw] at hx; exact dg_stepN r vs hvs x hx
      have hwm := (hall w (by simp)).2
      obtain ⟨x, hx, e, hm⟩ := ih w.curG (ws.map VR.dec) (w.k - 1) (w.w - w.k) (outP c r p)
          (by rw [(dg_curG w).2]; exact hwm)
          (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
              rw [(dg_dec y).2]; exact (hall y (by simp [hy])).2)
      simp only [List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨y, hy, rfl⟩
      · obtain ⟨⟨z, hz, e2⟩, _⟩ := hall w (by simp)
        exact ⟨z, by simp [hz], by show (loopRun n w.curG (ws.map VR.dec) (w.k - 1) (w.w - w.k) (outP c r p)).c'.dg = _; rw [e, (dg_curG w).1, e2], hm⟩
      · obtain ⟨⟨z, hz, e2⟩, _⟩ := hall y (by simp [hy])
        exact ⟨z, by simp [hz], by show (loopRun n w.curG (ws.map VR.dec) (w.k - 1) (w.w - w.k) (outP c r p)).c'.dg = _; rw [e, (dg_dec y).1, e2], hm⟩

theorem dg_outRec (c : VR) (r : Nat) : (outRec c r).dg = c.dg := by
  unfold outRec; split <;> simp [VR.dg]

theorem dg_nextPass (c : VR) (x : Nat) : (c.nextPass x).dg = c.dg ∧ (c.nextPass x).m = c.m := by
  simp [VR.nextPass, VR.dg]


theorem dg_stepList_pos : ∀ vs : List VR, (∀ x ∈ vs, x.m = 0) →
    (stepList vs).map VR.dg = vs.map VR.dg ∧ ∀ x ∈ stepList vs, x.m = 0
  | [], _ => by simp [stepList]
  | v :: vs, h => by
    have hv : v.m = 0 := h v (by simp)
    have h1 := dg_vis v.inc (by show v.m = 0; exact hv)
    refine ⟨?_, ?_⟩
    · simp only [stepList, List.map_cons, List.map_map, h1.1]
      rw [(dg_inc v).1]
      congr 1
      exact List.map_congr_left (fun y hy => (dg_vis y (h y (by simp [hy]))).1)
    · intro x hx
      simp only [stepList, List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨y, hy, rfl⟩
      · exact h1.2
      · exact (dg_vis y (h y (by simp [hy]))).2

theorem dg_stepN_pos (r : Nat) : ∀ vs : List VR, (∀ x ∈ vs, x.m = 0) →
    (stepN r vs).map VR.dg = vs.map VR.dg ∧ ∀ x ∈ stepN r vs, x.m = 0 := by
  induction r with
  | zero => intro vs h; exact ⟨by simp [stepN], by simpa [stepN] using h⟩
  | succ r ih =>
    intro vs h
    have h1 := dg_stepList_pos vs h
    have h2 := ih (stepList vs) h1.2
    exact ⟨by rw [stepN, h2.1, h1.1], by rw [stepN]; exact h2.2⟩

theorem dg_loopRun_pos : ∀ (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat),
    c.m = 0 → (∀ x ∈ vs, x.m = 0) → vs.length = n →
    (loopRun n c vs r s p).cs.map (fun t => t.1.dg) ++ [(loopRun n c vs r s p).c'.dg] = (c :: vs).map VR.dg := by
  intro n
  induction n with
  | zero =>
    intro c vs r s p hc hvs hl
    have : vs = [] := List.length_eq_zero_iff.mp hl
    subst this; simp [loopRun]
  | succ n ih =>
    intro c vs r s p hc hvs hl
    have hlen := stepN_length r vs
    obtain ⟨hmap, hmz⟩ := dg_stepN_pos r vs hvs
    unfold loopRun
    split
    · rename_i hw
      rw [hw] at hlen; simp at hlen; omega
    · rename_i w ws hw
      rw [hw] at hmap hmz
      have hwm : w.m = 0 := hmz w (by simp)
      have hwsm : ∀ x ∈ ws, x.m = 0 := fun x hx => hmz x (by simp [hx])
      have hlws : (ws.map VR.dec).length = n := by
        rw [hw] at hlen; simp at hlen ⊢; omega
      have := ih w.curG (ws.map VR.dec) (w.k - 1) (w.w - w.k) (outP c r p)
        (by rw [(dg_curG w).2]; exact hwm)
        (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
            rw [(dg_dec y).2]; exact hwsm y hy) hlws
      simp only [List.map_cons] at hmap
      simp only [List.map_cons, List.cons_append, List.map_map] at this ⊢
      rw [dg_outRec]
      have e : ws.map (VR.dg ∘ VR.dec) = ws.map VR.dg := List.map_congr_left (fun y _ => (dg_dec y).1)
      rw [(dg_curG w).1, e] at this
      rw [this, ← hmap]


theorem loopRun_cs_length : ∀ (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat),
    vs.length = n → (loopRun n c vs r s p).cs.length = n := by
  intro n
  induction n with
  | zero => intro c vs r s p hl; simp [loopRun]
  | succ n ih =>
    intro c vs r s p hl
    have hlen := stepN_length r vs
    unfold loopRun
    split
    · rename_i hw; rw [hw] at hlen; simp at hlen; omega
    · rename_i w ws hw
      rw [hw] at hlen; simp at hlen
      have := ih w.curG (ws.map VR.dec) (w.k - 1) (w.w - w.k) (outP c r p) (by simp; omega)
      simpa using this

theorem dg_runAll_pos (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat) (hc : c.m = 0)
    (hvs : ∀ x ∈ vs, x.m = 0) (hl : vs.length = n) :
    (((loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
        (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]).map fun t => t.1.dg) = (c :: vs).map VR.dg := by
  have h := dg_loopRun_pos n c vs r s p hc hvs hl
  simp only [List.map_append, List.map_cons, List.map_nil, dg_outRec]
  simpa using h


/-- Digit data of an odometer record. -/
def ORec.dgO (o : ORec) : DG := (o.d, o.r - o.d - 1, o.z + o.k - 1, o.m, (o.acc.length, o.O))

theorem toO_dgO (t : VR) (r s : Nat) (h : r + 1 + s = t.w) : (t.toO r s).dgO = t.dg := by
  simp [VR.toO, ORec.dgO, VR.dg]; omega

def TapeOut (T : List Nat) : Prop :=
  ∃ (u : List Nat) (pre' : List Rc), GoodW u ∧ (∀ x ∈ pre', x.Ok) ∧ pre' ≠ [] ∧ T = u ++ tailB pre'

theorem tapeOut_of (u : List Nat) (hu : GoodW u) (cs : List (VR × Nat × Nat)) (hcs : ∀ t ∈ cs, t.1.Ok)
    (hne : cs ≠ []) : TapeOut (u ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2)) :=
  ⟨u, _, hu, fun x hx => by
      simp only [List.mem_map] at hx; obtain ⟨t, ht, rfl⟩ := hx; exact t.1.done_ok (hcs t ht) _ _,
    by simpa using hne, rfl⟩

def TapeOutO (T : List Nat) : Prop :=
  ∃ (u : List Nat) (o : ORec) (os : List ORec), GoodW u ∧ (∀ x ∈ o :: os, x.Ok) ∧ T = u ++ sepRest (o :: os)

theorem tapeOutO_of (u : List Nat) (hu : GoodW u) (cs : List (VR × Nat × Nat))
    (hcs : ∀ t ∈ cs, t.1.Ok ∧ t.1.m = 0 ∧ t.2.1 + 1 + t.2.2 = t.1.w) (hne : cs ≠ []) :
    TapeOutO (u ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2)) := by
  rw [tailB_toO cs (fun t ht => ⟨(hcs t ht).1, (hcs t ht).2.1⟩)]
  cases cs with
  | nil => exact absurd rfl hne
  | cons t cs' =>
    refine ⟨u, t.1.toO t.2.1 t.2.2, cs'.map fun t => t.1.toO t.2.1 t.2.2, hu, ?_, by simp⟩
    intro x hx
    simp only [List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨q, hq, rfl⟩
    · exact toO_ok _ (hcs t (by simp)).1 _ _ (hcs t (by simp)).2.2
    · exact toO_ok _ (hcs q (by simp [hq])).1 _ _ (hcs q (by simp [hq])).2.2

def TapeOutD (D : List (DG)) (T : List Nat) : Prop :=
  ∃ (u : List Nat) (o : ORec) (os : List ORec), GoodW u ∧ (∀ x ∈ o :: os, x.Ok) ∧
    (∀ x ∈ o :: os, x.dgO ∈ D) ∧ T = u ++ sepRest (o :: os)

theorem TapeOutD.toO {D T} (h : TapeOutD D T) : TapeOutO T := by
  obtain ⟨u, o, os, a, b, _, c⟩ := h; exact ⟨u, o, os, a, b, c⟩

theorem TapeOutD.mono {D D' T} (h : TapeOutD D T) (hs : ∀ x ∈ D, x ∈ D') : TapeOutD D' T := by
  obtain ⟨u, o, os, a, b, c, d⟩ := h; exact ⟨u, o, os, a, b, fun x hx => hs _ (c x hx), d⟩

theorem tapeOutD_of (D : List (DG)) (u : List Nat) (hu : GoodW u) (cs : List (VR × Nat × Nat))
    (hcs : ∀ t ∈ cs, t.1.Ok ∧ t.1.m = 0 ∧ t.2.1 + 1 + t.2.2 = t.1.w) (hne : cs ≠ [])
    (hD : ∀ t ∈ cs, t.1.dg ∈ D) :
    TapeOutD D (u ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2)) := by
  rw [tailB_toO cs (fun t ht => ⟨(hcs t ht).1, (hcs t ht).2.1⟩)]
  cases cs with
  | nil => exact absurd rfl hne
  | cons t cs' =>
    refine ⟨u, t.1.toO t.2.1 t.2.2, cs'.map fun t => t.1.toO t.2.1 t.2.2, hu, ?_, ?_, by simp⟩
    · intro x hx
      simp only [List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨q, hq, rfl⟩
      · exact toO_ok _ (hcs t (by simp)).1 _ _ (hcs t (by simp)).2.2
      · exact toO_ok _ (hcs q (by simp [hq])).1 _ _ (hcs q (by simp [hq])).2.2
    · intro x hx
      simp only [List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨q, hq, rfl⟩
      · rw [toO_dgO _ _ _ (hcs t (by simp)).2.2]; exact hD t (by simp)
      · rw [toO_dgO _ _ _ (hcs q (by simp [hq])).2.2]; exact hD q (by simp [hq])

theorem tapeOutD_ex (D : List (DG)) (cs : List (VR × Nat × Nat))
    (hcs : ∀ t ∈ cs, t.1.Ok ∧ t.1.m = 0 ∧ t.2.1 + 1 + t.2.2 = t.1.w) (hne : cs ≠ [])
    (hD : ∀ t ∈ cs, t.1.dg ∈ D) :
    ∃ (o : ORec) (os : List ORec), (∀ x ∈ o :: os, x.Ok) ∧ (∀ x ∈ o :: os, x.dgO ∈ D) ∧
      tailB (cs.map fun t => t.1.done t.2.1 t.2.2) = sepRest (o :: os) := by
  rw [tailB_toO cs (fun t ht => ⟨(hcs t ht).1, (hcs t ht).2.1⟩)]
  cases cs with
  | nil => exact absurd rfl hne
  | cons t cs' =>
    refine ⟨t.1.toO t.2.1 t.2.2, cs'.map fun t => t.1.toO t.2.1 t.2.2, ?_, ?_, by simp⟩
    · intro x hx
      simp only [List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨q, hq, rfl⟩
      · exact toO_ok _ (hcs t (by simp)).1 _ _ (hcs t (by simp)).2.2
      · exact toO_ok _ (hcs q (by simp [hq])).1 _ _ (hcs q (by simp [hq])).2.2
    · intro x hx
      simp only [List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨q, hq, rfl⟩
      · rw [toO_dgO _ _ _ (hcs t (by simp)).2.2]; exact hD t (by simp)
      · rw [toO_dgO _ _ _ (hcs q (by simp [hq])).2.2]; exact hD q (by simp [hq])

/-- The successful outcome: parameters `Wf 1 S 1 Q'' 1 2^b'`, then the finished records. -/
def SuOut (D : List (DG)) (Wf Q'' : List Nat) (b : Nat) (T : List Nat) : Prop :=
  ∃ (S0 : List Nat) (o : ORec) (os : List ORec), BitsD S0 ∧
    GoodW (Wf ++ 1 :: (S0 ++ 1 :: (Q'' ++ 1 :: List.replicate b 2))) ∧
    (∀ x ∈ o :: os, x.Ok) ∧ (o :: os).map ORec.dgO = D ∧
    T = (Wf ++ 1 :: (S0 ++ 1 :: (Q'' ++ 1 :: List.replicate b 2))) ++ sepRest (o :: os)

/-- The refuted outcome: parameters `Wf 1 S0 1 Qp 3^a' 2 2^b'` (`a' + 1 + b' = N`), then the finished records. -/
def OdOut (D : List (DG)) (Wf Qp : List Nat) (N P : Nat) (R' : List Nat) : Prop :=
  ∃ (S0 : List Nat) (a' b' : Nat) (o : ORec) (os : List ORec), BitsD S0 ∧ S0 ≠ [] ∧ S0.length = P ∧ a' + 1 + b' = N ∧
    GoodW (Wf ++ 1 :: (S0 ++ 1 :: (Qp ++ List.replicate a' 3 ++ 2 :: List.replicate b' 2))) ∧
    (∀ x ∈ o :: os, x.Ok) ∧ (o :: os).map ORec.dgO = D ∧
    (Wf ++ [1]) ++ R' = (Wf ++ 1 :: (S0 ++ 1 :: (Qp ++ List.replicate a' 3 ++ 2 :: List.replicate b' 2))) ++ sepRest (o :: os)

theorem OdOut.toO {D Wf Qp N P R'} (h : OdOut D Wf Qp N P R') : TapeOutO ((Wf ++ [1]) ++ R') := by
  obtain ⟨S0, a', b', o, os, a, b, l, c, g, ok, d, e⟩ := h
  exact ⟨_, o, os, g, ok, e⟩

theorem tapeOutP_ex (cs : List (VR × Nat × Nat))
    (hcs : ∀ t ∈ cs, t.1.Ok ∧ t.1.m = 0 ∧ t.2.1 + 1 + t.2.2 = t.1.w) (hne : cs ≠ []) :
    ∃ (o : ORec) (os : List ORec), (∀ x ∈ o :: os, x.Ok) ∧ (o :: os).map ORec.dgO = cs.map (fun t => t.1.dg) ∧
      tailB (cs.map fun t => t.1.done t.2.1 t.2.2) = sepRest (o :: os) := by
  rw [tailB_toO cs (fun t ht => ⟨(hcs t ht).1, (hcs t ht).2.1⟩)]
  cases cs with
  | nil => exact absurd rfl hne
  | cons t cs' =>
    refine ⟨t.1.toO t.2.1 t.2.2, cs'.map fun t => t.1.toO t.2.1 t.2.2, ?_, ?_, by simp⟩
    · intro x hx
      simp only [List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨q, hq, rfl⟩
      · exact toO_ok _ (hcs t (by simp)).1 _ _ (hcs t (by simp)).2.2
      · exact toO_ok _ (hcs q (by simp [hq])).1 _ _ (hcs q (by simp [hq])).2.2
    · simp only [List.map_cons, List.map_map]
      congr 1
      · exact toO_dgO _ _ _ (hcs t (by simp)).2.2
      · apply List.map_congr_left
        intro q hq
        exact toO_dgO _ _ _ (hcs q (by simp [hq])).2.2

theorem dg_runAll (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat) (hc : c.m = 0)
    (hvs : ∀ x ∈ vs, x.m = 0) :
    ∀ t ∈ (loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
        (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')], t.1.dg ∈ (c :: vs).map VR.dg := by
  intro t ht
  simp only [List.mem_append, List.mem_singleton] at ht
  rcases ht with ht | rfl
  · obtain ⟨x, hx, e⟩ := dg_loopRun n c vs r s p hc hvs t ht
    rw [e]; exact List.mem_map_of_mem hx
  · obtain ⟨x, hx, e, _⟩ := dg_loopRun_c n c vs r s p hc hvs
    show (outRec _ _).dg ∈ _
    rw [dg_outRec, e]; exact List.mem_map_of_mem hx

theorem nn_eq (a b : Nat) : List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2 = NnTail a (b + 1) := by
  have key : ∀ (a : Nat) (L : List Nat), List.replicate a 3 ++ 3 :: L = List.replicate (a + 1) 3 ++ L := by
    intro a L; induction a with
    | zero => simp
    | succ a ih => simp [List.replicate_succ, ih]
  rw [key]; simp [NnTail, List.replicate_succ]


theorem tapeOutO_sym4 {T : List Nat} (h : TapeOutO T) : Sym4 T := by
  obtain ⟨u, o, os, hu, hos, rfl⟩ := h
  have : sepRest (o :: os) = 1 :: 1 :: tapeL (o :: os) := rfl
  exact hu.sym4.app (by
    rw [this]
    exact Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) (tapeL_sym4 _ hos)))

/-- A refuted assignment moves to the next one (`WI0`) or overflows (`BEEP`). -/
theorem odlNext (Wf : List Nat) (hW : BitsD Wf) (R' : List Nat) (hT : TapeOutO ((Wf ++ [1]) ++ R')) :
    (∃ u v os' X R'', Rest u v ∧ X ++ 3 :: R'' = (v ++ [1, 1]) ++ tapeL os' ∧
      znttLogic.Reach (hd QNTT.ODL (Wf ++ [1]) R') (hd QNTT.WI0 X (3 :: R''))) ∨
    (∃ A, znttLogic.Reach (hd QNTT.ODL (Wf ++ [1]) R') (hd QNTT.BEEP A [])) := by
  have sT := tapeOutO_sym4 hT
  have hR : Sym4 R' := (Sym4_app_iff.1 sT).2
  have hL : NoB (Wf ++ [1]) := NoB_app_iff.2 ⟨hW.noB, by intro x hx; simp at hx; simp [hx, NB]⟩
  obtain ⟨u, o, os, hu, hos, hXY⟩ := hT
  have hXY' : (Wf ++ [1]) ++ R' = u ++ 1 :: 1 :: tapeL (o :: os) := hXY
  obtain ⟨v, hv, h1, h2⟩ := odFail u hu o os hos _ _ hXY' hL hR
  cases hs : odoStepR (o :: os) with
  | some os' =>
    obtain ⟨X, R'', e, hr⟩ := h1 os' hs
    exact Or.inl ⟨u, v, os', X, R'', hv, e, hr⟩
  | none => exact Or.inr ⟨_, h2 hs⟩


theorem ORec.Ok.noB {o : ORec} (h : o.Ok) : NoB o.tape := by
  have a1 : (1 : Nat) ∈ NB := by simp [NB]
  have hf : BitsD [o.F, o.O, o.Pf] := by
    have hF := h.hF
    intro y hy; simp at hF hy; rcases hy with rfl | rfl | rfl <;> simp [hF]
  have hth : BitsD (therm o.d o.r) := by
    intro y hy; simp [therm, List.mem_replicate] at hy; rcases hy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
  unfold ORec.tape
  refine NoB_app_iff.2 ⟨hf.noB, ?_⟩
  simp only [NoB_cons_iff, NoB_app_iff]
  exact ⟨a1, h.acc.noB, a1, h.E.noB, a1, hth.noB, a1, (bitsD_winStr _ _ _).noB⟩

theorem sepRest_noB : ∀ os : List ORec, (∀ o ∈ os, o.Ok) → NoB (sepRest os)
  | [], _ => by simp [sepRest, NoB]
  | o :: os, h => by
    have a1 : (1 : Nat) ∈ NB := by simp [NB]
    simp only [sepRest, NoB_cons_iff, NoB_app_iff]
    exact ⟨a1, a1, (h o (by simp)).noB, sepRest_noB os (fun x hx => h x (by simp [hx]))⟩

theorem tapeL_noB (os : List ORec) (h : ∀ o ∈ os, o.Ok) : NoB (tapeL os) := by
  cases os with
  | nil => simp [tapeL, NoB]
  | cons o os => exact NoB_app_iff.2 ⟨(h o (by simp)).noB, sepRest_noB os (fun x hx => h x (by simp [hx]))⟩

/-- Success: the machine erases the records and restarts at `PA0` with `Nn` lengthened by the finished marks. -/
theorem sucRestart (D : List (DG)) (Wf Kf Cf : List Nat) (B : Nat) (T : List Nat)
    (hW : BitsD Wf) (hK : BitsD Kf) (hC : BitsD Cf) (h : SuOut D Wf (Kf ++ 1 :: Cf) (B + 1) T) :
    ∃ N : Nat, znttLogic.Reach (hdR QNTT.SU1 [] T)
      (hdR QNTT.PA0 [3] (1 :: (Kf ++ 1 :: (Cf ++ 1 :: (List.replicate (B + 2) 3 ++ List.replicate (N + 1) 0))))) := by
  obtain ⟨S0, o, os, hS, hg, hok, hd, rfl⟩ := h
  have hr := suOk Wf S0 Kf Cf (List.replicate B 2) (tapeL (o :: os)) hW hS hK hC (BitsD.rep B 2 (by simp))
    (by simpa [List.replicate_succ', List.append_assoc] using hg) (tapeL_noB _ hok)
  refine ⟨(tapeL (o :: os)).length, ?_⟩
  simp only [List.length_replicate] at hr
  simpa [sepRest, tapeL, List.replicate_succ', List.append_assoc] using hr


theorem ORec.vr_ok (o : ORec) (ho : o.Ok) (x : Nat) (hx : x ∈ [2, 3]) (hacc : 2 ≤ o.acc.length) :
    (o.vr x).Ok := by
  have hO : o.O ∈ [2, 3] := by
    have := ho.hF; simp at this; simpa using this.2.1
  refine { F := by simp [ORec.vr], O := hO, P := hx, k1 := ?_, kw := ?_, E := ?_, Elen := ?_, Elw := ?_ }
  · simp [ORec.vr]; split <;> omega
  · simp [ORec.vr]; split <;> omega
  · intro y hy
    simp [ORec.vr, List.mem_replicate] at hy
    rcases hy with rfl | h
    · simp
    · simp [h.2]
  · simp [ORec.vr]
  · have := ho.Elw; have := ho.Elen; simp [ORec.vr]; omega

theorem vr_cmp (o : ORec) :
    (o.vr 3).O = 3 → ∃ z, 1 ≤ (o.vr 3).k ∧ (o.vr 3).E = fld ((o.vr 3).k + z) (o.vr 3).k := by
  intro _
  refine ⟨o.E.length - 2, by simp [ORec.vr], ?_⟩
  simp [ORec.vr, fld]


/-- First assignment: `WI0` (witness initialisation) through the pass start to the cursor on record 0 (`RFL`). -/
theorem firstEntry (L R Pm Pm' : List Nat) (hL : NoB L) (hRest : Rest Pm Pm') (hP' : GoodW Pm')
    (r : Rc) (hr : r.Ok) (rs : List Rc) (hrs : ∀ x ∈ rs, x.Ok)
    (hLR : L ++ R = Pm ++ 1 :: 1 :: (r.body ++ tailB rs))
    (o : ORec) (os : List ORec) (hok : ∀ x ∈ o :: os, x.Ok) (hacc : ∀ x ∈ o :: os, 2 ≤ x.acc.length)
    (hk : ∀ x ∈ o :: os, 1 ≤ x.k) (hdr : ∀ x ∈ o :: os, x.d + 1 ≤ x.r)
    (h0 : r.initB 3 = (o.toRc 3).body) (h1 : tailI rs = tailB (os.map fun x => x.toRc 2))
    (hPS0 : (o.toRc 3).PS) (hPS : ∀ x ∈ os, (x.toRc 2).PS) :
    znttLogic.Reach (hd QNTT.WI0 L R)
      (hd QNTT.RFL (curTapeG Pm' [] (o.vr 3).curG 0 ((o.vr 3).k - 1) ((o.vr 3).w - (o.vr 3).k)
        ((os.map fun x => x.vr 2).map VR.dec)) []) := by
  have hwi := witnessInit L R Pm Pm' hL hRest r hr rs hrs hLR
  rw [h0, h1] at hwi
  have hrs0 : ∀ x ∈ os.map (fun x => x.toRc 2), x.PS := by
    intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx; exact hPS y hy
  have hN1 : NoB [1, 1] := by intro a ha; simp at ha; simp [ha, NB]
  have hL2 : NoB (Pm' ++ [1, 1] ++ (o.toRc 3).body ++ tailB (os.map fun x => x.toRc 2)) := by
    simp only [NoB_app_iff]
    exact ⟨⟨⟨hP'.noB, hN1⟩, Rc.body_noB _ hPS0.ok⟩, tailB_noB _ (fun x hx => (hrs0 x hx).ok)⟩
  have hps := passStartAll (Pm' ++ [1, 1] ++ (o.toRc 3).body ++ tailB (os.map fun x => x.toRc 2)) Pm'
    hL2 hP' (o.toRc 3) hPS0 (os.map fun x => x.toRc 2) hrs0 (by simp)
  have hBr : ∀ p ∈ (os.map fun x => (x, 2)), BrOk p := by
    intro p hp; simp only [List.mem_map] at hp; obtain ⟨y, hy, rfl⟩ := hp
    exact ⟨hk y (by simp [hy]), hacc y (by simp [hy]), by simp, hdr y (by simp [hy])⟩
  have e1 := toRc_ps_vr o 3 (hk o (by simp)) (hacc o (by simp)) (by simp) (hdr o (by simp))
  have e2 := tailP_vr (os.map fun x => (x, 2)) hBr
  simp only [List.map_map, Function.comp_def] at e2
  have hw : (o.vr 3).Ok := ORec.vr_ok o (hok o (by simp)) 3 (by simp) (hacc o (by simp))
  have hws : ∀ x ∈ (os.map fun x => x.vr 2), x.Ok := by
    intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
    exact ORec.vr_ok y (hok y (by simp [hy])) 2 (by simp) (hacc y (by simp [hy]))
  have hLe : Pm' ++ [1, 1] ++ (o.toRc 3).ps.body ++ tailP (os.map fun x => x.toRc 2) =
      Pm' ++ 1 :: 1 :: ([(o.vr 3).F, (o.vr 3).O, (o.vr 3).P] ++ 1 :: ((o.vr 3).tl ++ tailVR (os.map fun x => x.vr 2))) := by
    have : tailP (os.map fun x => x.toRc 2) = tailVR (os.map fun x => x.vr 2) := e2
    rw [this]
    have e1' : 1 :: 1 :: (o.toRc 3).ps.body = (o.vr 3).recd := e1
    simp only [VR.recd] at e1'
    have e3 : (o.toRc 3).ps.body = (o.vr 3).F :: (o.vr 3).O :: (o.vr 3).P :: 1 :: (o.vr 3).tl := by
      simpa using e1'
    rw [e3]; simp
  have hNL : NoB (Pm' ++ [1, 1] ++ (o.toRc 3).ps.body ++ tailP (os.map fun x => x.toRc 2)) := by
    rw [hLe]
    simp only [NoB_app_iff, NoB_cons_iff]
    refine ⟨hP'.noB, by simp [NB], by simp [NB], ?_⟩
    have h3 := hw.hdr3.noB
    simp only [NoB_cons_iff] at h3
    exact ⟨⟨h3.1, h3.2.1, h3.2.2.1, by intro a ha; simp at ha⟩, by simp [NB], hw.tl_noB, tailVR_noB _ hws⟩
  have hf := faG' _ Pm' hNL hP' (o.vr 3) hw _ hws (vr_cmp o) hLe
  exact hwi.trans (hps.trans hf)



/-- The record produced by the build, with header second cell `h1` and pointer size `j'`. -/
def recRc (j h1 j' : Nat) : Rc :=
  { F := 2, O := h1, Pf := 2, acc := 3 :: List.replicate j 2, E := 3 :: List.replicate j 2,
    b0 := 3, br := List.replicate j 2, u0 := 3, ur := List.replicate j' 2 }

theorem recH_body (j h1 j' : Nat) : recH h1 j j' 3 = 1 :: 1 :: (recRc j h1 j').body := by
  simp [recH, recRc, Rc.body, Rc.tlr, Rc.tl0, Dcopy, List.replicate_succ]

theorem recsFlat_tailB (j : Nat) (ps : List (Nat × Nat)) :
    recsFlat j 3 ps = tailB (ps.map fun q => recRc j q.1 q.2) := by
  induction ps with
  | nil => simp [recsFlat, tailB]
  | cons q ps ih =>
    simp only [recsFlat, List.map_cons, List.flatten_cons, tailB] at ih ⊢
    rw [ih, recH_body]; rfl

/-- The odometer record of a build record (`d = 0`, window at the start). -/
def recO (j : Nat) (q : Nat × Nat) : ORec :=
  { F := 2, O := q.1, Pf := 2, acc := 3 :: List.replicate j 2, E := 3 :: List.replicate j 2,
    d := 0, r := j + 1, z := 0, k := 1, m := q.2 }

theorem recO_init (j : Nat) (q : Nat × Nat) (x : Nat) (hj : 1 ≤ j) :
    (recRc j q.1 q.2).initB x = ((recO j q).toRc x).body := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp [Rc.initB, Rc.body, Rc.tlr, Rc.tl0, recRc, recO, ORec.toRc, therm, winStr, List.replicate_succ]

theorem recO_tail (j : Nat) (hj : 1 ≤ j) (ps : List (Nat × Nat)) :
    tailI (ps.map fun q => recRc j q.1 q.2) = tailB (ps.map fun q => (recO j q).toRc 2) := by
  induction ps with
  | nil => simp [tailI, tailB]
  | cons q ps ih =>
    simp only [List.map_cons, tailI, tailB] at ih ⊢
    rw [ih, recO_init j q 2 hj]


theorem Rest.app {u v w z : List Nat} (h : Rest u v) (h2 : Rest w z) : Rest (u ++ w) (v ++ z) := by
  induction h with
  | nil => simpa using h2
  | bit hb _ ih => exact Rest.bit hb ih
  | mb hb _ ih => exact Rest.mb hb ih

theorem Rest.goodW {u v : List Nat} (h : Rest u v) : GoodW v := by
  induction h with
  | nil => exact GoodW.nil
  | bit hb _ ih => exact GoodW.bit (by simp) ih
  | mb hb _ ih => exact GoodW.mb (by simp) ih

theorem rest_rep (a : Nat) : Rest (List.replicate a 3) (List.replicate a 3) := by
  induction a with
  | zero => exact Rest.nil
  | succ a ih => exact Rest.bit (by simp) ih

theorem rest_blk (a : Nat) : Rest (1 :: List.replicate (a + 1) 3) (1 :: List.replicate (a + 1) 3) := by
  simpa [List.replicate_succ] using Rest.mb (b := 3) (by simp) (rest_rep a)


theorem bd32 (j : Nat) : BitsD (3 :: List.replicate j 2) := BitsD.cons (by simp) (BitsD.rep _ _ (by simp))

theorem recRc_ok (j h1 j' : Nat) (hj : 1 ≤ j) (h : h1 ∈ [2, 3]) : (recRc j h1 j').Ok :=
  { F := by simp [recRc], O := h, Pf := by simp [recRc], acc := bd32 j, E := bd32 j,
    Elen := by simp [recRc]; omega, b0 := by simp [recRc], br := BitsD.rep _ _ (by simp),
    u0 := by simp [recRc], ur := BitsD.rep _ _ (by simp) }

theorem recO_ok (j : Nat) (q : Nat × Nat) (hj : 1 ≤ j) (h : q.1 ∈ [2, 3]) : (recO j q).Ok :=
  { hF := by simp [recO] at h ⊢; simpa using h, acc := bd32 j, E := bd32 j,
    d := by simp [recO], k := by simp [recO], Elen := by simp [recO]; omega, Elw := by simp [recO] }

theorem recO_ps (j : Nat) (q : Nat × Nat) (x : Nat) (hj : 1 ≤ j) (h : q.1 ∈ [2, 3]) (hx : x ∈ [2, 3]) :
    ((recO j q).toRc x).PS := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hk : 1 ≤ (recO (i + 1) q).k := by simp [recO]
  refine ⟨⟨by simp [ORec.toRc, recO], by simpa [ORec.toRc, recO] using h, hx,
      by simpa [ORec.toRc, recO] using bd32 (i + 1), ?_, by simp [ORec.toRc, recO],
      by simp [ORec.toRc, recO, therm], ?_, by simp [ORec.toRc, recO, winStr], ?_⟩,
    by simp [ORec.toRc, recO], toRc_rest _ x hk⟩
  · intro y hy; simp [ORec.toRc, recO, List.mem_replicate] at hy
    rcases hy with rfl | h
    · simp
    · simp [h.2]
  · intro y hy; simp [ORec.toRc, recO, therm, List.mem_replicate] at hy; simp [hy]
  · intro y hy; simp [ORec.toRc, recO, winStr, List.mem_replicate] at hy; simp [hy]

theorem roundsPs_ne (n : Nat) : ∀ (c w0 : Nat) (ps : List (Nat × Nat)), (ps ≠ [] ∨ 0 < c) →
    roundsPs n c w0 ps ≠ [] := by
  intro c
  induction c with
  | zero =>
    intro w0 ps h
    rcases h with h | h
    · simpa [roundsPs] using h
    · omega
  | succ c ih =>
    intro w0 ps _
    simp only [roundsPs]
    refine ih _ _ (Or.inl ?_)
    simp [newRecs]


/-- From the record build to the first-pass cursor: the build's records are the odometer records `recO`. -/
theorem buildEntry (j c n : Nat) (hj : 1 ≤ j) (hc : 0 < c) :
    ∃ (o : ORec) (os : List ORec), o :: os = (roundsPs n c 1 []).map (recO j) ∧
    znttLogic.Reach
      (hd QNTT.WX [0, 3] (1 :: (List.replicate (j + 1) 3 ++ 1 :: (List.replicate (2 + 1) 3 ++ 1 ::
        (List.replicate c 3 ++ 1 :: List.replicate (n + 1) 3)))))
      (hd QNTT.RFL (curTapeG (Pfx (wEnd n c 1 + 1) j 2 ++ List.replicate (0 + c) 3 ++ 1 :: List.replicate (n + 1) 3) []
        (o.vr 3).curG 0 ((o.vr 3).k - 1) ((o.vr 3).w - (o.vr 3).k) ((os.map fun x => x.vr 2).map VR.dec)) []) := by
  have hb := recordBuild j 2 c n hc
  have hok := roundsPs_ok n c 1 [] (by simp)
  obtain ⟨q, ps, hqs⟩ : ∃ q ps, roundsPs n c 1 [] = q :: ps := by
    cases h : roundsPs n c 1 [] with
    | nil => exact absurd h (roundsPs_ne n c 1 [] (Or.inr hc))
    | cons q ps => exact ⟨q, ps, rfl⟩
  rw [hqs] at hb hok
  have hq : ∀ x ∈ q :: ps, x.1 ∈ [2, 3] := hok
  refine ⟨recO j q, ps.map (recO j), by simp [hqs], ?_⟩
  have hRest : Rest (Pfx (wEnd n c 1 + 1) j 2 ++ List.replicate (0 + c) 3 ++ 1 :: List.replicate (n + 1) 3) (Pfx (wEnd n c 1 + 1) j 2 ++ List.replicate (0 + c) 3 ++ 1 :: List.replicate (n + 1) 3) := by
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have := ((rest_rep (wEnd n (c' + 1) 1 + 1)).app (rest_blk (j' + 1))).app
      ((rest_blk 2).app ((rest_blk c').app (rest_blk n)))
    have e : Pfx (wEnd n (c' + 1) 1 + 1) (j' + 1) 2 ++ List.replicate (0 + (c' + 1)) 3 ++ 1 :: List.replicate (n + 1) 3 =
        List.replicate (wEnd n (c' + 1) 1 + 1) 3 ++ (1 :: List.replicate (j' + 1 + 1) 3) ++
          ((1 :: List.replicate (2 + 1) 3) ++ ((1 :: List.replicate (c' + 1) 3) ++ (1 :: List.replicate (n + 1) 3))) := by
      simp [Pfx, List.append_assoc]
    rw [e]; exact this
  have hq0 : q.1 ∈ [2, 3] := hq q (by simp)
  have hqs' : ∀ x ∈ ps, x.1 ∈ [2, 3] := fun x hx => hq x (by simp [hx])
  have hrs : ∀ x ∈ ps.map (fun x => recRc j x.1 x.2), x.Ok := by
    intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
    exact recRc_ok j _ _ hj (hqs' y hy)
  have hL : NoB (Pfx (wEnd n c 1 + 1) j 2 ++ List.replicate (0 + c) 3) := by
    simp only [Pfx, NoB_app_iff, NoB_cons_iff, NoB_rep_iff]; simp [NB]
  have hLR : (Pfx (wEnd n c 1 + 1) j 2 ++ List.replicate (0 + c) 3) ++
      (1 :: (List.replicate (n + 1) 3 ++ recsFlat j (2 + 1) (q :: ps))) =
      (Pfx (wEnd n c 1 + 1) j 2 ++ List.replicate (0 + c) 3 ++ 1 :: List.replicate (n + 1) 3) ++ 1 :: 1 :: ((recRc j q.1 q.2).body ++ tailB (ps.map fun x => recRc j x.1 x.2)) := by
    rw [recsFlat_tailB]
    simp [tailB, List.append_assoc]
  have hos : ∀ x ∈ recO j q :: ps.map (recO j), x.Ok := by
    intro x hx; simp only [List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨y, hy, rfl⟩
    · exact recO_ok j q hj hq0
    · exact recO_ok j y hj (hqs' y hy)
  have hfe := firstEntry (Pfx (wEnd n c 1 + 1) j 2 ++ List.replicate (0 + c) 3)
    (1 :: (List.replicate (n + 1) 3 ++ recsFlat j (2 + 1) (q :: ps))) (Pfx (wEnd n c 1 + 1) j 2 ++ List.replicate (0 + c) 3 ++ 1 :: List.replicate (n + 1) 3) (Pfx (wEnd n c 1 + 1) j 2 ++ List.replicate (0 + c) 3 ++ 1 :: List.replicate (n + 1) 3) hL hRest hRest.goodW
    (recRc j q.1 q.2) (recRc_ok j _ _ hj hq0) (ps.map fun x => recRc j x.1 x.2) hrs hLR
    (recO j q) (ps.map (recO j)) hos
    (by intro x hx; simp only [List.mem_cons, List.mem_map] at hx
        rcases hx with rfl | ⟨y, hy, rfl⟩ <;> simp [recO] <;> omega)
    (by intro x hx; simp only [List.mem_cons, List.mem_map] at hx
        rcases hx with rfl | ⟨y, hy, rfl⟩ <;> simp [recO])
    (by intro x hx; simp only [List.mem_cons, List.mem_map] at hx
        rcases hx with rfl | ⟨y, hy, rfl⟩ <;> simp [recO])
    (recO_init j q 3 hj)
    (by rw [recO_tail j hj ps]; simp [Function.comp_def])
    (recO_ps j q 3 hj hq0 (by simp))
    (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
        exact recO_ps j y 2 hj (hqs' y hy) (by simp))
  exact hb.trans hfe



theorem rest_map {u v : List Nat} (h : Rest u v) : v = u.map (fun x => if x = 1 then 1 else 3) := by
  induction h with
  | nil => rfl
  | bit hb _ ih =>
    simp at hb; rcases hb with rfl | rfl <;> simp [ih]
  | mb hb _ ih =>
    simp at hb; rcases hb with rfl | rfl <;> simp [ih]

/-- The overflow state (the machine's beep) steps left over the last cell, then the erase sweep restarts. -/
theorem beepToSU1 (A : List Nat) (hA : NoB A) (hne : A ≠ []) :
    ∃ X, znttLogic.zstep (hd QNTT.BEEP A []) = some X ∧ znttLogic.Reach X (hdR QNTT.SU1 [] A) := by
  obtain ⟨A', c, rfl⟩ : ∃ A' c, A = A' ++ [c] := by
    rcases List.eq_nil_or_concat A with h | ⟨A', c, h⟩
    · exact absurd h hne
    · exact ⟨A', c, by simpa using h⟩
  have hc : c ∈ [1, 2, 3] := by
    have := hA c (by simp); simpa [NB] using this
  have hA' : NoB A' := fun x hx => hA x (by simp [hx])
  have h2 := su0Scan A' [c] hA' (by
    intro x hx; simp at hx; subst hx; simp at hc; rcases hc with rfl | rfl | rfl <;> simp [ALL])
  exact ⟨_, beepStepC A' [] c hc, by simpa using h2⟩

theorem bits_map {w : List Nat} (h : BitsD w) : BitsD (w.map (fun x => if x = 1 then 1 else 3)) := by
  intro y hy
  simp only [List.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have := h x hx; simp at this; rcases this with rfl | rfl <;> simp

theorem resetAll_ok : ∀ os : List ORec, (∀ x ∈ os, x.Ok) → ∀ x ∈ resetAll os, x.Ok
  | [], _ => by simp [resetAll]
  | o :: os, h => by
    intro x hx
    simp only [resetAll, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact (h o (by simp)).reset
    · exact resetAll_ok os (fun y hy => h y (by simp [hy])) x hx

/-- An odometer record as a tape record. -/
def orcRc (o : ORec) : Rc :=
  { F := o.F, O := o.O, Pf := o.Pf, acc := o.acc, E := o.E, b0 := (therm o.d o.r).headD 2,
    br := (therm o.d o.r).tail, u0 := (winStr o.z o.k o.m).headD 2, ur := (winStr o.z o.k o.m).tail }

theorem therm_cons (d r : Nat) : (therm d r).headD 2 :: (therm d r).tail = therm d r := by
  cases h : therm d r with
  | nil => simp [therm] at h
  | cons a l => simp

theorem winStr_cons (z k m : Nat) (hk : 1 ≤ k) : (winStr z k m).headD 2 :: (winStr z k m).tail = winStr z k m := by
  cases h : winStr z k m with
  | nil => obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩; simp [winStr, hj, List.replicate_succ] at h
  | cons a l => simp

theorem orcRc_body (o : ORec) (hk : 1 ≤ o.k) : (orcRc o).body = o.tape := by
  have hT : (therm o.d o.r) ≠ [] := by simp [therm]
  have hW : (winStr o.z o.k o.m) ≠ [] := by
    obtain ⟨j, hj⟩ : ∃ j, o.k = j + 1 := ⟨o.k - 1, by omega⟩
    simp [winStr, hj, List.replicate_succ]
  simp only [Rc.body, Rc.tlr, Rc.tl0, orcRc, ORec.tape]
  generalize therm o.d o.r = Tm at hT ⊢
  generalize winStr o.z o.k o.m = Wm at hW ⊢
  cases Tm with
  | nil => exact absurd rfl hT
  | cons a T =>
    cases Wm with
    | nil => exact absurd rfl hW
    | cons b U => simp

theorem orcRc_init (o : ORec) (x : Nat) : (orcRc o).initB x = (o.toRc x).body := by
  simp only [Rc.initB, Rc.body, Rc.tlr, Rc.tl0, orcRc, ORec.toRc]


theorem therm_bits (d r : Nat) : BitsD (therm d r) := by
  intro y hy; simp [therm, List.mem_replicate] at hy; rcases hy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp

theorem ORec.Ok.hF3 {o : ORec} (h : o.Ok) : o.F ∈ [2, 3] ∧ o.O ∈ [2, 3] ∧ o.Pf ∈ [2, 3] := by
  have := h.hF; simp at this; simpa using this

theorem bits_headD {l : List Nat} (h : BitsD l) : l.headD 2 ∈ [2, 3] := by
  cases l with
  | nil => simp
  | cons a l => exact h a (by simp)

theorem bits_tail {l : List Nat} (h : BitsD l) : BitsD l.tail := by
  cases l with
  | nil => exact h
  | cons a l => intro x hx; exact h x (List.mem_cons_of_mem a hx)

theorem orcRc_ok (o : ORec) (ho : o.Ok) : (orcRc o).Ok := by
  obtain ⟨hF, hO, hP⟩ := ho.hF3
  exact ⟨hF, hO, hP, ho.acc, ho.E, ho.Elen, bits_headD (therm_bits o.d o.r), bits_tail (therm_bits o.d o.r),
    bits_headD (bitsD_winStr o.z o.k o.m), bits_tail (bitsD_winStr o.z o.k o.m)⟩

theorem toRc_ps (o : ORec) (ho : o.Ok) (hacc : 2 ≤ o.acc.length) (x : Nat) (hx : x ∈ [2, 3]) : (o.toRc x).PS := by
  obtain ⟨hF, hO, hP⟩ := ho.hF3
  refine ⟨⟨hF, hO, hx, ho.acc, ?_, by simp [ORec.toRc],
    bits_headD (therm_bits o.d o.r), bits_tail (therm_bits o.d o.r),
    bits_headD (bitsD_winStr o.z o.k o.m), bits_tail (bitsD_winStr o.z o.k o.m)⟩, hacc, toRc_rest o x ho.k⟩
  intro y hy; simp [ORec.toRc, List.mem_replicate] at hy
  rcases hy with rfl | h
  · simp
  · simp [h.2]

theorem tailB_orc : ∀ os : List ORec, (∀ x ∈ os, 1 ≤ x.k) → tailB (os.map orcRc) = sepRest os
  | [], _ => by simp [tailB, sepRest]
  | o :: os, h => by
    simp only [List.map_cons, tailB, sepRest]
    rw [orcRc_body o (h o (by simp)), tailB_orc os (fun x hx => h x (by simp [hx]))]

theorem tailI_orc : ∀ os : List ORec, tailI (os.map orcRc) = tailB (os.map fun x => x.toRc 2)
  | [] => by simp [tailI, tailB]
  | o :: os => by
    simp only [List.map_cons, tailI, tailB]
    rw [orcRc_init, tailI_orc os]

/-- The next assignment: from `WI0` on the reset records to the first-pass cursor. -/
theorem nextEntry (X R'' v : List Nat) (hNoB : NoB X) (hv : Rest v v) (o : ORec) (os : List ORec)
    (hok : ∀ x ∈ o :: os, x.Ok) (hacc : ∀ x ∈ o :: os, 2 ≤ x.acc.length)
    (e : X ++ 3 :: R'' = (v ++ [1, 1]) ++ tapeL (o :: os)) :
    znttLogic.Reach (hd QNTT.WI0 X (3 :: R''))
      (hd QNTT.RFL (curTapeG v [] (o.vr 3).curG 0 ((o.vr 3).k - 1) ((o.vr 3).w - (o.vr 3).k)
        ((os.map fun x => x.vr 2).map VR.dec)) []) := by
  have hks : ∀ x ∈ os, 1 ≤ x.k := fun x hx => (hok x (by simp [hx])).k
  have hr := orcRc_ok o (hok o (by simp))
  have hrs : ∀ x ∈ os.map orcRc, x.Ok := by
    intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
    exact orcRc_ok y (hok y (by simp [hy]))
  have hLR : X ++ 3 :: R'' = v ++ 1 :: 1 :: ((orcRc o).body ++ tailB (os.map orcRc)) := by
    rw [e, orcRc_body o (hok o (by simp)).k, tailB_orc os hks]
    simp [tapeL, sepRest, List.append_assoc]
  exact firstEntry X (3 :: R'') v v hNoB hv hv.goodW (orcRc o) hr (os.map orcRc) hrs hLR o os hok hacc
    (fun x hx => (hok x hx).k) (fun x hx => (hok x hx).d) (orcRc_init o 3) (tailI_orc os)
    (toRc_ps o (hok o (by simp)) (hacc o (by simp)) 3 (by simp))
    (fun x hx => toRc_ps x (hok x (by simp [hx])) (hacc x (by simp [hx])) 2 (by simp))


/-! ## Compare mismatch: refutation at the output compare -/


/-- `cpRound`s while the accumulator is the smaller: `n` rounds leave one accumulator mark and `d + 2` marks of `E`. -/
theorem cmpLt (A : List Nat) (d : Nat) : ∀ (n a s z : Nat) (R : List Nat), Sym4 A → Sym4 R →
    znttLogic.Reach
      (hdR QNTT.CP0 (A ++ [1]) (List.replicate a 2 ++ List.replicate (n + 1) 3 ++ List.replicate s 2 ++
        1 :: (List.replicate (n + d + 2) 3 ++ List.replicate z 2) ++ 1 :: R))
      (hdR QNTT.CP0 (A ++ [1]) (List.replicate (a + n) 2 ++ 3 :: List.replicate s 2 ++
        1 :: (List.replicate (d + 2) 3 ++ List.replicate (z + n) 2) ++ 1 :: R)) := by
  intro n
  induction n with
  | zero => intro a s z R hA hR; simpa using (LTM.Reach.refl _ _)
  | succ n ih =>
    intro a s z R hA hR
    have h := cpRound A a (n + d + 1) z (List.replicate n 3 ++ List.replicate s 2) R hA
      (bd_app (BitsD.rep n 3 (by simp)) (BitsD.rep s 2 (by simp))) hR
    have ih' := ih (a + 1) s (z + 1) R hA hR
    rw [show a + 1 + n = a + (n + 1) by omega, show z + 1 + n = z + (n + 1) by omega] at ih'
    rw [show n + 1 + d + 2 = n + d + 3 by omega]
    simp only [List.append_assoc, List.cons_append, List.replicate_succ] at h ih' ⊢
    exact h.trans ih'

/-- Accumulator smaller than `E`: refuted at `CPE3`. -/
theorem cpLtEnd (A : List Nat) (a s d z : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach
      (hdR QNTT.CP0 (A ++ [1]) (List.replicate a 2 ++ 3 :: List.replicate s 2 ++
        1 :: (List.replicate (d + 2) 3 ++ List.replicate z 2) ++ 1 :: R))
      (hd QNTT.ODL (A ++ [1] ++ List.replicate a 2 ++ [3] ++ List.replicate s 2 ++ [1] ++ [3])
        (3 :: (List.replicate d 3 ++ List.replicate z 2 ++ 1 :: R))) := by
  have sP : Sym4 (A ++ [1]) := hA.app (sym4_cell 1 (by simp))
  have sZ : Sym4 (List.replicate z 2) := (BitsD.rep z 2 (by simp)).sym4
  have sS : Sym4 (List.replicate s 2) := (BitsD.rep s 2 (by simp)).sym4
  have sA2 : Sym4 (List.replicate a 2) := (BitsD.rep a 2 (by simp)).sym4
  have sD : Sym4 (List.replicate d 3) := (BitsD.rep d 3 (by simp)).sym4
  have g1 := cp0Skip (A ++ [1]) a (3 :: (List.replicate s 2 ++ 1 :: (List.replicate (d + 2) 3 ++ List.replicate z 2 ++ 1 :: R))) sP
    (by simp [ALL, sS, sZ, sD, hR])
  have g2 := cp0Hit (A ++ [1] ++ List.replicate a 2) (List.replicate s 2 ++ 1 :: (List.replicate (d + 2) 3 ++ List.replicate z 2 ++ 1 :: R))
    (by simp [ALL, hA, sA2]) (by simp [ALL, sS, sZ, sD, hR])
  have g3 := cpe1 (A ++ [1] ++ List.replicate a 2 ++ [3]) s (List.replicate (d + 2) 3 ++ List.replicate z 2 ++ 1 :: R)
    (by simp [ALL, hA, sA2]) (by simp [ALL, sZ, sD, hR])
  have g4 := cpe2One (A ++ [1] ++ List.replicate a 2 ++ [3] ++ List.replicate s 2 ++ [1])
    (List.replicate (d + 1) 3 ++ List.replicate z 2 ++ 1 :: R)
    (by simp [ALL, hA, sA2, sS]) (by simp [ALL, sZ, sD, hR])
  have g5 := cpe3One (A ++ [1] ++ List.replicate a 2 ++ [3] ++ List.replicate s 2 ++ [1] ++ [3])
    (List.replicate d 3 ++ List.replicate z 2 ++ 1 :: R)
    (by simp [ALL, hA, sA2, sS]) (by simp [ALL, sZ, sD, hR])
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.replicate_succ] at g1 g2 g3 g4 g5 ⊢
  exact g1.trans (g2.trans (g3.trans (g4.trans g5)))

/-- Accumulator larger than `E`: refuted at `CP5`. -/
theorem cpGtEnd (A : List Nat) (a : Nat) (f : List Nat) (z : Nat) (R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach
      (hdR QNTT.CP0 (A ++ [1]) (List.replicate a 2 ++ 3 :: 3 :: f ++ 1 :: (3 :: List.replicate z 2 ++ 1 :: R)))
      (hd QNTT.ODL (A ++ [1] ++ List.replicate a 2 ++ [2] ++ (3 :: f) ++ [1] ++ [3])
        (List.replicate z 2 ++ 1 :: R)) := by
  have sP : Sym4 (A ++ [1]) := hA.app (sym4_cell 1 (by simp))
  have sQ : Sym4 (A ++ [1] ++ List.replicate a 2) := sP.app (BitsD.rep a 2 (by simp)).sym4
  have hf3 : BitsD (3 :: f) := BitsD.cons (by simp) hf
  have sZ : Sym4 (List.replicate z 2) := (BitsD.rep z 2 (by simp)).sym4
  have sf : Sym4 f := hf.sym4
  have h1 := cp0Skip (A ++ [1]) a (3 :: 3 :: (f ++ 1 :: ((3 :: List.replicate z 2) ++ 1 :: R))) sP
    (by simp [ALL, sf, hR, sZ])
  have h2 := cp0Hit (A ++ [1] ++ List.replicate a 2) (3 :: (f ++ 1 :: ((3 :: List.replicate z 2) ++ 1 :: R))) sQ
    (by simp [ALL, sf, hR, sZ])
  have h3 := cp1Two (A ++ [1] ++ List.replicate a 2) (f ++ 1 :: ((3 :: List.replicate z 2) ++ 1 :: R)) sQ
    (by simp [ALL, sf, hR, sZ])
  have h4 := cp2Mark (A ++ [1] ++ List.replicate a 2) (3 :: (f ++ 1 :: ((3 :: List.replicate z 2) ++ 1 :: R))) sQ
    (by simp [ALL, sf, hR, sZ])
  have h5 := cp3Skip (A ++ [1] ++ List.replicate a 2 ++ [2]) (3 :: f) ((3 :: List.replicate z 2) ++ 1 :: R)
    (by simp [ALL, hA, sQ]) hf3 (by simp [ALL, hR, sZ])
  have h6 := cp4One (A ++ [1] ++ List.replicate a 2 ++ [2] ++ (3 :: f) ++ [1]) (List.replicate z 2 ++ 1 :: R)
    (by simp [ALL, hA, sQ, sf]) (by simp [ALL, hR, sZ])
  have h7 : znttLogic.Reach (hdR QNTT.CP5 (A ++ [1] ++ List.replicate a 2 ++ [2] ++ (3 :: f) ++ [1] ++ [3]) (List.replicate z 2 ++ 1 :: R))
      (hd QNTT.ODL (A ++ [1] ++ List.replicate a 2 ++ [2] ++ (3 :: f) ++ [1] ++ [3]) (List.replicate z 2 ++ 1 :: R)) := by
    cases z with
    | zero =>
      have := cp5M (A ++ [1] ++ List.replicate a 2 ++ [2] ++ (3 :: f) ++ [1] ++ [3]) R (by simp [ALL, hA, sQ, sf]) hR
      simpa only [List.replicate_zero, List.nil_append] using this
    | succ k =>
      have := cp5Zero (A ++ [1] ++ List.replicate a 2 ++ [2] ++ (3 :: f) ++ [1] ++ [3])
        (List.replicate k 2 ++ 1 :: R) (by simp [ALL, hA, sQ, sf]) (by simp [ALL, hR, sZ])
      simpa only [List.replicate_succ, List.cons_append] using this
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 h4 h5 h6 h7 ⊢
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))

theorem cmpGt (A : List Nat) (d : Nat) : ∀ (e a s z : Nat) (R : List Nat), Sym4 A → Sym4 R →
    znttLogic.Reach
      (hdR QNTT.CP0 (A ++ [1]) (List.replicate a 2 ++ List.replicate (e + d + 2) 3 ++ List.replicate s 2 ++
        1 :: (List.replicate (e + 1) 3 ++ List.replicate z 2) ++ 1 :: R))
      (hdR QNTT.CP0 (A ++ [1]) (List.replicate (a + e) 2 ++ List.replicate (d + 2) 3 ++ List.replicate s 2 ++
        1 :: (3 :: List.replicate (z + e) 2) ++ 1 :: R)) := by
  intro e
  induction e with
  | zero => intro a s z R hA hR; simpa using (LTM.Reach.refl _ _)
  | succ e ih =>
    intro a s z R hA hR
    have h := cpRound A a e z (List.replicate (e + d + 1) 3 ++ List.replicate s 2) R hA
      (bd_app (BitsD.rep _ 3 (by simp)) (BitsD.rep s 2 (by simp))) hR
    have ih' := ih (a + 1) s (z + 1) R hA hR
    rw [show a + 1 + e = a + (e + 1) by omega, show z + 1 + e = z + (e + 1) by omega] at ih'
    rw [show e + 1 + d + 2 = e + d + 3 by omega]
    simp only [List.append_assoc, List.cons_append, List.replicate_succ] at h ih' ⊢
    exact h.trans ih'

theorem cmpAccLt (A : List Nat) (n d a s z : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach
      (hdR QNTT.CP0 (A ++ [1]) (List.replicate a 2 ++ List.replicate (n + 1) 3 ++ List.replicate s 2 ++
        1 :: (List.replicate (n + d + 2) 3 ++ List.replicate z 2) ++ 1 :: R))
      (hd QNTT.ODL (A ++ [1] ++ List.replicate (a + n) 2 ++ [3] ++ List.replicate s 2 ++ [1] ++ [3])
        (3 :: (List.replicate d 3 ++ List.replicate (z + n) 2 ++ 1 :: R))) :=
  (cmpLt A d n a s z R hA hR).trans (cpLtEnd A (a + n) s d (z + n) R hA hR)

theorem cmpAccGt (A : List Nat) (e d a s z : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach
      (hdR QNTT.CP0 (A ++ [1]) (List.replicate a 2 ++ List.replicate (e + d + 2) 3 ++ List.replicate s 2 ++
        1 :: (List.replicate (e + 1) 3 ++ List.replicate z 2) ++ 1 :: R))
      (hd QNTT.ODL (A ++ [1] ++ List.replicate (a + e) 2 ++ [2] ++ (3 :: (List.replicate d 3 ++ List.replicate s 2)) ++ [1] ++ [3])
        (List.replicate (z + e) 2 ++ 1 :: R)) := by
  have h1 := cmpGt A d e a s z R hA hR
  have h2 := cpGtEnd A (a + e) (List.replicate d 3 ++ List.replicate s 2) (z + e) R hA
    (bd_app (BitsD.rep d 3 (by simp)) (BitsD.rep s 2 (by simp))) hR
  simp only [List.append_assoc, List.cons_append, List.replicate_succ] at h1 h2 ⊢
  exact h1.trans h2


theorem fa0OLt (A : List Nat) (w : Rc) (hw : w.DE) (hO : w.O = 3) (n d s z : Nat)
    (hacc : w.acc = List.replicate (n + 1) 3 ++ List.replicate s 2)
    (hE : w.E = List.replicate (n + d + 2) 3 ++ List.replicate z 2)
    (ws : List Rc) (hws : ∀ x ∈ ws, x.DE) (hA : Sym4 A) :
    znttLogic.Reach (hdR QNTT.FA0 A ([w.F, w.O, w.Pf] ++ 1 :: (w.tl ++ tailB ws)))
      (hd QNTT.ODL (A ++ [3, 3, w.Pf] ++ [1] ++ List.replicate n 2 ++ [3] ++ List.replicate s 2 ++ [1] ++ [3])
        (3 :: (List.replicate d 3 ++ List.replicate (z + n) 2 ++ 1 :: (w.b0 :: (w.br ++ 1 :: w.u0 :: w.ur) ++ tailB ws)))) := by
  have ho := hw.ok
  have sTl : Sym4 (w.tl ++ tailB ws) := (w.tl_sym4 ho).app (tailB_sym4 ws (fun x hx => (hws x hx).ok))
  have sA3 : Sym4 (A ++ [3]) := hA.app (sym4_cell 3 (by simp))
  have h4 := fa0Mark A w.F (w.O :: w.Pf :: 1 :: (w.tl ++ tailB ws)) ho.F hA
    (sym4_B ho.O (sym4_B ho.Pf (sym4_M sTl)))
  have h5 := fa1o (A ++ [3]) (w.Pf :: 1 :: (w.tl ++ tailB ws)) sA3 (sym4_B ho.Pf (sym4_M sTl))
  have h6 := faoSkip (A ++ [3] ++ [3]) [w.Pf] (w.tl ++ tailB ws) (sA3.app (sym4_cell 3 (by simp)))
    (fun y hy => by simp at hy; subst hy; exact ho.Pf) sTl
  have sR' : Sym4 (w.b0 :: (w.br ++ 1 :: w.u0 :: w.ur) ++ tailB ws) := by
    have := sTl
    simp only [Rc.tl] at this
    simp [hacc, hE] at this
    simpa using this.2.2.2.2.2.2
  have hwt : w.tl ++ tailB ws = List.replicate 0 2 ++ List.replicate (n + 1) 3 ++ List.replicate s 2 ++
      1 :: (List.replicate (n + d + 2) 3 ++ List.replicate z 2) ++ 1 :: (w.b0 :: (w.br ++ 1 :: w.u0 :: w.ur) ++ tailB ws) := by
    simp [Rc.tl, hacc, hE]
  rw [hwt] at h4 h5 h6 ⊢
  have h7 := cmpAccLt (A ++ [3] ++ [3] ++ [w.Pf]) n d 0 s z (w.b0 :: (w.br ++ 1 :: w.u0 :: w.ur) ++ tailB ws)
    ((sA3.app (sym4_cell 3 (by simp))).app (sym4_B ho.Pf Sym4.nil)) sR'
  simp only [hO, List.append_assoc, List.cons_append, List.nil_append] at h4 h5 h6 h7 ⊢
  refine h4.trans (h5.trans (h6.trans (h7.of_eq rfl ?_)))
  simp [Rc.tl, hacc, List.replicate_succ, Nat.add_comm, Nat.add_left_comm]

theorem fa0OGt (A : List Nat) (w : Rc) (hw : w.DE) (hO : w.O = 3) (e d s z : Nat)
    (hacc : w.acc = List.replicate (e + d + 2) 3 ++ List.replicate s 2)
    (hE : w.E = List.replicate (e + 1) 3 ++ List.replicate z 2)
    (ws : List Rc) (hws : ∀ x ∈ ws, x.DE) (hA : Sym4 A) :
    znttLogic.Reach (hdR QNTT.FA0 A ([w.F, w.O, w.Pf] ++ 1 :: (w.tl ++ tailB ws)))
      (hd QNTT.ODL (A ++ [3, 3, w.Pf] ++ [1] ++ List.replicate e 2 ++ [2] ++ (3 :: (List.replicate d 3 ++ List.replicate s 2)) ++ [1] ++ [3])
        (List.replicate (z + e) 2 ++ 1 :: (w.b0 :: (w.br ++ 1 :: w.u0 :: w.ur) ++ tailB ws))) := by
  have ho := hw.ok
  have sTl : Sym4 (w.tl ++ tailB ws) := (w.tl_sym4 ho).app (tailB_sym4 ws (fun x hx => (hws x hx).ok))
  have sA3 : Sym4 (A ++ [3]) := hA.app (sym4_cell 3 (by simp))
  have h4 := fa0Mark A w.F (w.O :: w.Pf :: 1 :: (w.tl ++ tailB ws)) ho.F hA
    (sym4_B ho.O (sym4_B ho.Pf (sym4_M sTl)))
  have h5 := fa1o (A ++ [3]) (w.Pf :: 1 :: (w.tl ++ tailB ws)) sA3 (sym4_B ho.Pf (sym4_M sTl))
  have h6 := faoSkip (A ++ [3] ++ [3]) [w.Pf] (w.tl ++ tailB ws) (sA3.app (sym4_cell 3 (by simp)))
    (fun y hy => by simp at hy; subst hy; exact ho.Pf) sTl
  have sR' : Sym4 (w.b0 :: (w.br ++ 1 :: w.u0 :: w.ur) ++ tailB ws) := by
    have := sTl
    simp only [Rc.tl] at this
    simp [hacc, hE] at this
    simpa using this.2.2.2.2.2.2
  have hwt : w.tl ++ tailB ws = List.replicate 0 2 ++ List.replicate (e + d + 2) 3 ++ List.replicate s 2 ++
      1 :: (List.replicate (e + 1) 3 ++ List.replicate z 2) ++ 1 :: (w.b0 :: (w.br ++ 1 :: w.u0 :: w.ur) ++ tailB ws) := by
    simp [Rc.tl, hacc, hE]
  rw [hwt] at h4 h5 h6 ⊢
  have h7 := cmpAccGt (A ++ [3] ++ [3] ++ [w.Pf]) e d 0 s z (w.b0 :: (w.br ++ 1 :: w.u0 :: w.ur) ++ tailB ws)
    ((sA3.app (sym4_cell 3 (by simp))).app (sym4_B ho.Pf Sym4.nil)) sR'
  simp only [hO, List.append_assoc, List.cons_append, List.nil_append] at h4 h5 h6 h7 ⊢
  refine h4.trans (h5.trans (h6.trans (h7.of_eq rfl ?_)))
  simp [Rc.tl, hacc, List.replicate_succ, Nat.add_comm, Nat.add_left_comm]


/-- The refuted outcome, generalised: the parameter region `Nn` is `3^a' 2^b'`, and the tape is given whole. -/
def OdOut' (D : List (DG)) (Wf Qp : List Nat) (N P : Nat) (T : List Nat) : Prop :=
  ∃ (S0 : List Nat) (a' b' : Nat) (o : ORec) (os : List ORec), BitsD S0 ∧ S0 ≠ [] ∧ S0.length = P ∧ a' + b' = N ∧ 1 ≤ N ∧
    GoodW (Wf ++ 1 :: (S0 ++ 1 :: (Qp ++ List.replicate a' 3 ++ List.replicate b' 2))) ∧
    (∀ x ∈ o :: os, x.Ok) ∧ (o :: os).map ORec.dgO = D ∧
    T = (Wf ++ 1 :: (S0 ++ 1 :: (Qp ++ List.replicate a' 3 ++ List.replicate b' 2))) ++ sepRest (o :: os)

theorem OdOut'.toO {D Wf Qp N P T} (h : OdOut' D Wf Qp N P T) : TapeOutO T := by
  obtain ⟨S0, a', b', o, os, a, b, l, c, c1, g, ok, d, e⟩ := h
  exact ⟨_, o, os, g, ok, e⟩

theorem OdOut'.noB {D Wf Qp N P T} (h : OdOut' D Wf Qp N P T) : NoB T := by
  obtain ⟨S0, a', b', o, os, a, b, l, c, c1, g, ok, d, e⟩ := h
  rw [e]
  have sr : sepRest (o :: os) = 1 :: 1 :: tapeL (o :: os) := rfl
  refine NoB_app_iff.2 ⟨g.noB, ?_⟩
  rw [sr]
  exact fun x hx => by
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · simp [NB]
    · simp [NB]
    · exact tapeL_noB _ ok x hx

theorem OdOut.to' {D Wf Qp N P R'} (h : OdOut D Wf Qp N P R') : OdOut' D Wf Qp N P ((Wf ++ [1]) ++ R') := by
  obtain ⟨S0, a', b', o, os, hS, hne, hl, hN, hg, hos, hd, e⟩ := h
  refine ⟨S0, a', b' + 1, o, os, hS, hne, hl, by omega, by omega, by simpa [List.replicate_succ] using hg, hos, hd, ?_⟩
  simpa [List.replicate_succ] using e

def StepNone (D : List (DG)) : Prop :=
  ∃ (o : ORec) (os : List ORec), (∀ x ∈ o :: os, x.Ok) ∧ (o :: os).map ORec.dgO = D ∧ odoStepR (o :: os) = none

def StepInfo (D : List (DG)) (Wf Kf Cf : List Nat) (N P : Nat) (v : List Nat) (os' : List ORec) : Prop :=
  ∃ (S0 : List Nat) (a' b' : Nat) (o : ORec) (os : List ORec), BitsD S0 ∧ S0 ≠ [] ∧ S0.length = P ∧ a' + b' = N ∧ 1 ≤ N ∧
    (∀ x ∈ o :: os, x.Ok) ∧ (o :: os).map ORec.dgO = D ∧ odoStepR (o :: os) = some os' ∧
    v = (Wf ++ 1 :: (S0 ++ 1 :: ((Kf ++ 1 :: Cf) ++ [1] ++ List.replicate a' 3 ++ List.replicate b' 2))).map
      (fun x => if x = 1 then 1 else 3)

theorem odlNext3 (D : List (DG)) (Wf Kf Cf : List Nat) (hW : BitsD Wf) (hK : BitsD Kf) (hC : BitsD Cf)
    (N P : Nat) (L R' : List Nat) (hT : OdOut' D Wf ((Kf ++ 1 :: Cf) ++ [1]) N P (L ++ R')) :
    (∃ u v os' X R'', Rest u v ∧ StepInfo D Wf Kf Cf N P v os' ∧ X ++ 3 :: R'' = (v ++ [1, 1]) ++ tapeL os' ∧
      znttLogic.Reach (hd QNTT.ODL L R') (hd QNTT.WI0 X (3 :: R''))) ∨
    (∃ (A : List Nat) (n0 : Nat), StepNone D ∧ znttLogic.Reach (hd QNTT.ODL L R') (hd QNTT.BEEP A []) ∧
      ∃ X, znttLogic.zstep (hd QNTT.BEEP A []) = some X ∧
        znttLogic.Reach X (hdR QNTT.PA0 [3] (1 :: (Kf.map (fun x => if x = 1 then 1 else 3) ++ 1 ::
          ((Cf.map (fun x => if x = 1 then 1 else 3) ++ [3]) ++ 1 :: (List.replicate N 3 ++ List.replicate (n0 + 1) 0)))))) := by
  have hT' := hT.toO
  have sT := tapeOutO_sym4 hT'
  have hR : Sym4 R' := (Sym4_app_iff.1 sT).2
  have hL : NoB L := (NoB_app_iff.1 hT.noB).1
  obtain ⟨S0, a', b', o, os, hS0, hS0ne, hSP, hN, hN1, hg, hos, hdg, hXY⟩ := hT
  have hXY' : L ++ R' = (Wf ++ 1 :: (S0 ++ 1 :: ((Kf ++ 1 :: Cf) ++ [1] ++ List.replicate a' 3 ++ List.replicate b' 2))) ++
      1 :: 1 :: tapeL (o :: os) := hXY
  obtain ⟨v, hv, h1, h2⟩ := odFail _ hg o os hos _ _ hXY' hL hR
  cases hs : odoStepR (o :: os) with
  | some os' =>
    obtain ⟨X, R'', e, hr⟩ := h1 os' hs
    exact Or.inl ⟨_, v, os', X, R'', hv, ⟨S0, a', b', o, os, hS0, hS0ne, hSP, hN, hN1, hos, hdg, hs, by
      rw [rest_map hv]⟩, e, hr⟩
  | none =>
    right
    have hb := h2 hs
    have hvm := rest_map hv
    have hgv : GoodW v := hv.goodW
    have hrep : List.replicate a' 3 ++ List.replicate b' 3 = List.replicate N 3 := by
      subst hN
      rw [List.replicate_append_replicate]
    have hvE : v = Wf.map (fun x => if x = 1 then 1 else 3) ++ 1 :: (S0.map (fun x => if x = 1 then 1 else 3) ++ 1 ::
        (Kf.map (fun x => if x = 1 then 1 else 3) ++ 1 :: (Cf.map (fun x => if x = 1 then 1 else 3) ++ 1 :: List.replicate N 3))) := by
      rw [hvm, ← hrep]
      simp [List.map_append, List.map_replicate, List.append_assoc]
    obtain ⟨L0, rfl⟩ : ∃ L0, N = L0 + 1 := ⟨N - 1, by omega⟩
    have hrk : ∀ x ∈ resetAll (o :: os), x.Ok := resetAll_ok _ hos
    have hnb : NoB (tapeL (resetAll (o :: os))) := tapeL_noB _ hrk
    have hAeq : (v ++ [1, 1]) ++ tapeL (resetAll (o :: os)) =
        (Wf.map (fun x => if x = 1 then 1 else 3) ++ 1 :: (S0.map (fun x => if x = 1 then 1 else 3) ++ 1 ::
          (Kf.map (fun x => if x = 1 then 1 else 3) ++ 1 :: (Cf.map (fun x => if x = 1 then 1 else 3) ++ 1 ::
            List.replicate (L0 + 1) 3)))) ++ 1 :: 1 :: tapeL (resetAll (o :: os)) := by
      rw [hvE]; simp [List.append_assoc]
    have hnbA : NoB ((v ++ [1, 1]) ++ tapeL (resetAll (o :: os))) := by
      have h1 : NoB v := hgv.noB
      exact NoB_app_iff.2 ⟨NoB_app_iff.2 ⟨h1, by intro x hx; simp at hx; simp [hx, NB]⟩, hnb⟩
    have hne : (v ++ [1, 1]) ++ tapeL (resetAll (o :: os)) ≠ [] := by simp
    obtain ⟨X, hX, hXr⟩ := beepToSU1 _ hnbA hne
    have hbo := beepOk (Wf.map (fun x => if x = 1 then 1 else 3)) (S0.map (fun x => if x = 1 then 1 else 3))
      (Kf.map (fun x => if x = 1 then 1 else 3)) (Cf.map (fun x => if x = 1 then 1 else 3))
      (tapeL (resetAll (o :: os))) L0 (bits_map hW) (bits_map hS0) (bits_map hK) (bits_map hC)
      (by rw [← hvE]; exact hgv) hnb
    refine ⟨_, (tapeL (resetAll (o :: os))).length, ⟨o, os, hos, hdg, hs⟩, hb, X, hX, ?_⟩
    rw [hAeq] at hXr
    exact hXr.trans hbo



theorem VR.toRc_bu (v : VR) (hv : v.Ok) :
    v.toRc.b0 :: (v.toRc.br ++ 1 :: v.toRc.u0 :: v.toRc.ur) = v.b ++ 1 :: v.u := by
  obtain ⟨b0, br, hB⟩ := List.exists_cons_of_ne_nil hv.bne
  obtain ⟨u0, ur, hU⟩ := List.exists_cons_of_ne_nil hv.une
  simp [VR.toRc, VR.toRcA, hB, hU]

theorem fa0GFail (A : List Nat) (w : VR) (hw : w.Ok) (ws : List VR) (hws : ∀ x ∈ ws, x.Ok) (hA : Sym4 A)
    (hO : w.O = 3) (e z : Nat) (he : 1 ≤ e) (hE : w.E = fld (e + z) e) (hne : e ≠ w.k) :
    ∃ (L R acc2 E2 : List Nat), BitsD acc2 ∧ BitsD E2 ∧ acc2.length = w.w ∧ E2.length = w.E.length ∧
      znttLogic.Reach (hdR QNTT.FA0 A ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws))) (hd QNTT.ODL L R) ∧
      L ++ R = A ++ [3, w.O, w.P] ++ 1 :: (acc2 ++ 1 :: (E2 ++ 1 :: (w.b ++ 1 :: (w.u ++ tailVR ws)))) := by
  have hwd : w.toRc.DE := ⟨w.toRcA_ok hw _ (fld_bits _ _), w.toRcA_rest _⟩
  have hws' : ∀ x ∈ ws.map VR.toRc, x.DE := by
    intro x hx; simp only [List.mem_map] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨v.toRcA_ok (hws v hv) _ (fld_bits _ _), v.toRcA_rest _⟩
  have hkw := hw.kw
  have hk1 := hw.k1
  obtain ⟨n, hn⟩ : ∃ n, w.k = n + 1 := ⟨w.k - 1, by omega⟩
  have hbu := VR.toRc_bu w hw
  have hO' : w.toRc.O = 3 := by simpa [VR.toRc, VR.toRcA] using hO
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · -- e < k: E is smaller
    obtain ⟨d, hd⟩ : ∃ d, w.k = e + d + 1 := ⟨w.k - e - 1, by omega⟩
    obtain ⟨e', he'⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    have b6 := fa0OGt A w.toRc hwd hO' e' d (w.w - w.k) z
      (by have hk : w.k = e' + d + 2 := by omega
          simp [VR.toRc, VR.toRcA, fld, hk]) (by simp [VR.toRc, VR.toRcA, hE, fld, he'])
      (ws.map VR.toRc) hws' hA
    rw [VR.toRc_tl w hw, tailB_toRc ws hws, hbu] at b6
    have hlen : w.E.length = e + z := by rw [hE]; simp [fld]
    refine ⟨_, _, List.replicate e' 2 ++ 2 :: 3 :: (List.replicate d 3 ++ List.replicate (w.w - w.k) 2),
      3 :: List.replicate (z + e') 2, ?_, ?_, ?_, ?_, b6.of_eq rfl rfl, ?_⟩
    · exact bd_app (BitsD.rep _ _ (by simp)) (BitsD.cons (by simp) (BitsD.cons (by simp)
        (bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp)))))
    · exact BitsD.cons (by simp) (BitsD.rep _ _ (by simp))
    · simp; omega
    · simp [hlen]; omega
    · simp [VR.toRc, VR.toRcA, hO, List.append_assoc]
  · obtain ⟨d, hd⟩ : ∃ d, e = w.k + d + 1 := ⟨e - w.k - 1, by omega⟩
    have b6 := fa0OLt A w.toRc hwd hO' n d (w.w - w.k) z
      (by simp [VR.toRc, VR.toRcA, fld, hn]) (by have he2 : e = n + d + 2 := by omega
                                                 simp [VR.toRc, VR.toRcA, hE, fld, he2])
      (ws.map VR.toRc) hws' hA
    rw [VR.toRc_tl w hw, tailB_toRc ws hws, hbu] at b6
    have hlen : w.E.length = e + z := by rw [hE]; simp [fld]
    refine ⟨_, _, List.replicate n 2 ++ 3 :: List.replicate (w.w - w.k) 2,
      3 :: 3 :: (List.replicate d 3 ++ List.replicate (z + n) 2), ?_, ?_, ?_, ?_, b6.of_eq rfl rfl, ?_⟩
    · exact bd_app (BitsD.rep _ _ (by simp)) (BitsD.cons (by simp) (BitsD.rep _ _ (by simp)))
    · exact BitsD.cons (by simp) (BitsD.cons (by simp) (bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp))))
    · simp; omega
    · simp [hlen]; omega
    · simp [VR.toRc, VR.toRcA, hO, List.append_assoc]


theorem colAdvanceGF (c w : VR) (ws : List VR) (hc : c.Ok) (hw : w.Ok) (hws : ∀ x ∈ ws, x.Ok) (hF : c.F = 3)
    (hO : c.O = 2 ∨ c.O = 3) (hwO : w.O = 3) (e z : Nat) (he : 1 ≤ e) (hE : w.E = fld (e + z) e) (hne : e ≠ w.k)
    (Pm : List Nat) (hP : GoodW Pm) (pre : List Rc)
    (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2) (a s : Nat) :
    ∃ (L R acc2 E2 : List Nat), BitsD acc2 ∧ BitsD E2 ∧ acc2.length = w.w ∧ E2.length = w.E.length ∧
      znttLogic.Reach (hd QNTT.RFL (curTapeG Pm pre c a 0 s (w :: ws)) []) (hd QNTT.ODL L R) ∧
      L ++ R = Pm ++ tailB (pre ++ [c.done a s]) ++ [1, 1, 3, w.O, w.P, 1] ++
        (acc2 ++ 1 :: (E2 ++ 1 :: (w.b ++ 1 :: (w.u ++ tailVR ws)))) := by
  have hvs : ∀ x ∈ w :: ws, x.Ok := fun x hx => by
    simp at hx; rcases hx with rfl | hx
    · exact hw
    · exact hws x hx
  have sPm := hP.sym4
  have sPre : Sym4 (tailB pre) := tailB_sym4 pre (fun x hx => (hpre x hx).1)
  have s2 : ∀ j, Sym4 (List.replicate j 2) := fun j => (BitsD.rep j 2 (by simp)).sym4
  have hA := curToCA0 c hc hF hO Pm hP pre hpre a s (w :: ws) hvs
  have sU := hc.u.sym4
  have sB := hc.b.sym4
  have sE := hc.E.sym4
  have sW : Sym4 ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws)) :=
    hw.hdr3.sym4.app (sym4_M (hw.tl_sym4.app (tailVR_sym4 ws hws)))
  have sT : Sym4 (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR (w :: ws)))) := by
    refine sE.app (sym4_M (sB.app (sym4_M (sU.app ?_))))
    exact tailVR_sym4 (w :: ws) hvs
  have b4 := ca0Sweep (Pm ++ tailB pre ++ [1, 1, 3, c.O, c.P]) (List.replicate a 2 ++ [3])
    (List.replicate s 2 ++ 1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR (w :: ws)))))
    ((sPm.app sPre).app (sym4_M (sym4_M (sym4_B (by simp) (sym4_B hc.O (sym4_B hc.P Sym4.nil))))))
    (bd_app (BitsD.rep _ _ (by simp)) (fun x hx => by simp at hx; simp [hx])) ((s2 s).app (sym4_M sT))
  have b5 := caNext c hc (Pm ++ tailB pre) (List.replicate a 2 ++ 3 :: List.replicate s 2)
    ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws)) (sPm.app sPre)
    (bd_app (BitsD.rep _ _ (by simp)) (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all))
    (by cases a <;> simp [List.replicate_succ]) sW
  obtain ⟨L, R, acc2, E2, h1, h2, h3, h4, b6, hLR⟩ := fa0GFail
    (Pm ++ tailB pre ++ [1, 1, 2, c.O, c.P, 1] ++ (List.replicate a 2 ++ 3 :: List.replicate s 2) ++
      1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ [1, 1])))) w hw ws hws
    (((((sPm.app sPre).app (sym4_M (sym4_M (sym4_B (by simp) (sym4_B hc.O (sym4_B hc.P (sym4_M Sym4.nil))))))).app
      (BitsD.sym4 (bd_app (BitsD.rep _ _ (by simp)) (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all)))).app
      (sym4_M (sE.app (sym4_M (sB.app (sym4_M (sU.app (sym4_M (sym4_M Sym4.nil))))))))))
    hwO e z he hE hne
  have hdone : (c.done a s).body = [2, c.O, c.P] ++ 1 :: ((List.replicate a 2 ++ 3 :: List.replicate s 2) ++
      1 :: (c.E ++ 1 :: (c.b ++ 1 :: c.u))) := by
    have e : (c.done a s).tl = (c.toRcA (List.replicate a 2 ++ 3 :: List.replicate s 2)).tl := rfl
    rw [Rc.body_eq, e, VR.toRcA_tl c hc]
    rfl
  refine ⟨L, R, acc2, E2, h1, h2, h3, h4, ?_, ?_⟩
  · simp only [tailB_append, tailB, hdone, List.append_nil, curTapeG, List.append_assoc, List.cons_append,
      List.nil_append, List.replicate_succ] at hA b4 b5 b6 ⊢
    exact hA.trans (b4.trans (b5.trans b6))
  · rw [hLR]
    simp [tailB_append, tailB, hdone, List.append_assoc]


theorem colStepNF (c : VR) (hc : c.Ok) (hF : c.F = 3) (hO : c.O = 2) (Pm : List Nat) (hP : GoodW Pm)
    (pre : List Rc) (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2) (r s : Nat) (vs : List VR)
    (hvs : ∀ x ∈ vs, x.Ok) (w : VR) (ws : List VR) (hw : stepN r vs = w :: ws)
    (hwO : w.O = 3) (e z : Nat) (he : 1 ≤ e) (hE : w.E = fld (e + z) e) (hne : e ≠ w.k) :
    ∃ (L R acc2 E2 : List Nat), BitsD acc2 ∧ BitsD E2 ∧ acc2.length = w.w ∧ E2.length = w.E.length ∧
      znttLogic.Reach (hd QNTT.RFL (curTapeG Pm pre c 0 r s vs) []) (hd QNTT.ODL L R) ∧
      L ++ R = Pm ++ tailB (pre ++ [c.done r s]) ++ [1, 1, 3, w.O, w.P, 1] ++
        (acc2 ++ 1 :: (E2 ++ 1 :: (w.b ++ 1 :: (w.u ++ tailVR ws)))) := by
  have h1 := cursorLoop c hc hF hO Pm hP pre hpre s r 0 vs hvs
  rw [hw, Nat.zero_add] at h1
  have hok := stepN_ok r vs hvs
  rw [hw] at hok
  obtain ⟨L, R, a2, E2, k1, k2, k3, k4, hr, hLR⟩ := colAdvanceGF c w ws hc (hok w (by simp))
    (fun x hx => hok x (by simp [hx])) hF (Or.inl hO) hwO e z he hE hne Pm hP pre hpre r s
  rw [curTapeG_eq _ _ _ hO]
  rw [curTapeG_eq _ _ _ hO] at hr
  exact ⟨L, R, a2, E2, k1, k2, k3, k4, h1.trans hr, hLR⟩

theorem colStepOF (n : Nat) (c : VR) (hc : c.Ok) (hF : c.F = 3) (hO : c.O = 3) (hm : c.m = 0) (hn : c.n = n)
    (Wf : List Nat) (hW : BitsD Wf) (P2 : List Nat) (hP2 : GoodW (1 :: P2)) (pre : List Rc)
    (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2) (s wE : Nat) (hwE : 2 ≤ wE)
    (r : Nat) (p : Nat × Nat) (e0 : Nat) (hp : 1 ≤ p.2) (he0 : 1 ≤ e0) (hew : e0 ≤ wE) (hE0 : c.E = fld wE e0)
    (vs : List VR) (hvs : ∀ x ∈ vs, x.Ok) (w : VR) (ws : List VR) (hw : stepN r vs = w :: ws)
    (hwO : w.O = 3) (e z : Nat) (he : 1 ≤ e) (hE : w.E = fld (e + z) e) (hne : e ≠ w.k) :
    ∃ (L R acc2 E2 : List Nat), BitsD acc2 ∧ BitsD E2 ∧ acc2.length = w.w ∧ E2.length = w.E.length ∧
      znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: P2)) pre c 0 r s vs) [])
        (hd QNTT.ODL L R) ∧
      L ++ R = (Wf ++ 1 :: (List.replicate (sAdv (r * n) p).1 2 ++ List.replicate (sAdv (r * n) p).2 3 ++ 1 :: P2)) ++
        tailB (pre ++ [({ c with E := fld wE (eAdv wE (r * n) e0) } : VR).done r s]) ++ [1, 1, 3, w.O, w.P, 1] ++
        (acc2 ++ 1 :: (E2 ++ 1 :: (w.b ++ 1 :: (w.u ++ tailVR ws)))) := by
  have hwc : wE = c.w := by have := hc.Elw; rw [hE0, fld_len _ _ hew] at this; exact this
  have h1 := outLoop n c hc hF hO hm hn Wf hW P2 hP2 pre hpre s wE hwE hwc r 0 p e0 vs hvs hp he0 hew
  have hb := eAdv_bounds wE (r * n) e0 he0 hew
  have hElen := hc.Elen
  rw [hE0, fld_len _ _ hew] at hElen
  have hc' : ({ c with E := fld wE (eAdv wE (r * n) e0) } : VR).Ok :=
    { F := hc.F, O := hc.O, P := hc.P, k1 := hc.k1, kw := hc.kw, E := fld_bits _ _,
      Elen := by show 2 ≤ (fld wE (eAdv wE (r * n) e0)).length; rw [fld_len _ _ hb.2]; exact hElen,
      Elw := by show (fld wE (eAdv wE (r * n) e0)).length = _; rw [fld_len _ _ hb.2]; exact hwc }
  have hG := goodW_reg Wf (List.replicate (sAdv (r * n) p).1 2 ++ List.replicate (sAdv (r * n) p).2 3) P2 hW
    (bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp)))
    (by have := sAdv_pos (r * n) p hp; obtain ⟨q', hq'⟩ : ∃ q', (sAdv (r * n) p).2 = q' + 1 := ⟨(sAdv (r * n) p).2 - 1, by omega⟩
        simp [hq', List.replicate_succ]) hP2
  have hok := stepN_ok r vs hvs
  rw [hw] at hok
  obtain ⟨L, R, a2, E2, k1, k2, k3, k4, hr, hLR⟩ := colAdvanceGF ({ c with E := fld wE (eAdv wE (r * n) e0) } : VR) w ws hc'
    (hok w (by simp)) (fun x hx => hok x (by simp [hx])) hF (Or.inr hO) hwO e z he hE hne _ hG pre hpre r s
  rw [hw, Nat.zero_add] at h1
  refine ⟨L, R, a2, E2, k1, k2, k3, k4, (LTM.Reach.of_eq h1 ?_ ?_).trans hr, hLR⟩
  · simp [curTapeG, hE0, hO, List.append_assoc]
  · simp [curTapeG, hO, VR.b, VR.u, List.append_assoc]


/-- The output-node `E` register is a unary-marked string. -/
def EF (x : VR) : Prop := x.O = 3 → ∃ e, 1 ≤ e ∧ e ≤ x.E.length ∧ x.E = fld x.E.length e

theorem EF_of {x y : VR} (hE : x.E = y.E) (hO : x.O = y.O) (h : EF y) : EF x := by
  intro h3
  rw [hO] at h3
  obtain ⟨e, h1, h2, h4⟩ := h h3
  exact ⟨e, h1, by rw [hE]; exact h2, by rw [hE]; exact h4⟩

theorem vis_EO (v : VR) : v.vis.E = v.E ∧ v.vis.O = v.O := by unfold VR.vis; split <;> simp
theorem dec_EO (v : VR) : v.dec.E = v.E ∧ v.dec.O = v.O := by unfold VR.dec; split <;> simp

theorem stepList_EF : ∀ vs : List VR, (∀ x ∈ vs, EF x) → ∀ x ∈ stepList vs, EF x
  | [], _ => by simp [stepList]
  | v :: vs, h => by
    intro x hx
    simp only [stepList, List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨y, hy, rfl⟩
    · exact EF_of ((vis_EO _).1) ((vis_EO _).2) (EF_of rfl rfl (h v (by simp)) : EF v.inc)
    · exact EF_of ((vis_EO _).1) ((vis_EO _).2) (h y (by simp [hy]))

theorem stepN_EF (r : Nat) : ∀ vs : List VR, (∀ x ∈ vs, EF x) → ∀ x ∈ stepN r vs, EF x := by
  induction r with
  | zero => intro vs h; simpa [stepN] using h
  | succ r ih => intro vs h; exact ih _ (stepList_EF vs h)

theorem dec_EF (vs : List VR) (h : ∀ x ∈ vs, EF x) : ∀ x ∈ vs.map VR.dec, EF x := by
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact EF_of (dec_EO y).1 (dec_EO y).2 (h y hy)

theorem EF_mismatch (w : VR) (hw : w.Ok) (hEF : EF w) (hO : w.O = 3)
    (hn : ¬ (w.O = 3 → ∃ z, 1 ≤ w.k ∧ w.E = fld (w.k + z) w.k)) :
    ∃ e z, 1 ≤ e ∧ w.E = fld (e + z) e ∧ e ≠ w.k := by
  obtain ⟨e, h1, h2, h3⟩ := hEF hO
  have h5 : e + (w.E.length - e) = w.E.length := by omega
  refine ⟨e, w.E.length - e, h1, by rw [h5]; exact h3, ?_⟩
  intro hk
  apply hn
  intro _
  subst hk
  exact ⟨w.E.length - w.k, hw.k1, by rw [h5]; exact h3⟩

/-- A cursor-form record as an odometer record (digits are `therm`/`winStr`). -/
def VR.toOc (v : VR) : ORec :=
  { F := v.F, O := v.O, Pf := v.P, acc := fld v.w v.k, E := v.E,
    d := v.n, r := v.n + 1 + v.s, z := v.a, k := v.c + 1, m := v.t }

theorem VR.recd_toOc (v : VR) (hm : v.m = 0) : v.recd = 1 :: 1 :: v.toOc.tape := by
  have hb : v.b = therm v.n (v.n + 1 + v.s) := by simp [VR.b, therm, hm]
  have hu : v.u = winStr v.a (v.c + 1) v.t := by simp [VR.u, winStr]
  simp only [VR.recd, VR.tl, VR.toOc, ORec.tape, hb, hu]
  simp

theorem VR.toOc_ok (v : VR) (hv : v.Ok) : v.toOc.Ok :=
  { hF := by
      have h1 := hv.F; have h2 := hv.O; have h3 := hv.P
      simp at h1 h2 h3
      simp [VR.toOc]; omega,
    acc := fld_bits _ _, E := hv.E, d := by simp [VR.toOc], k := by simp [VR.toOc], Elen := hv.Elen,
    Elw := by have := fld_len v.w v.k hv.kw; have := hv.Elw; simp [VR.toOc, *] }

theorem VR.toOc_dg (v : VR) (hv : v.Ok) : v.toOc.dgO = v.dg := by
  have := fld_len v.w v.k hv.kw
  simp [VR.toOc, ORec.dgO, VR.dg, this]; omega

theorem sepRest_append : ∀ (l1 l2 : List ORec), sepRest (l1 ++ l2) = sepRest l1 ++ sepRest l2
  | [], l2 => by simp [sepRest]
  | o :: os, l2 => by simp [sepRest, sepRest_append os l2]

theorem tailVR_sepRest : ∀ (vs : List VR), (∀ x ∈ vs, x.m = 0) → tailVR vs = sepRest (vs.map VR.toOc)
  | [], _ => by simp [tailVR, sepRest]
  | v :: vs, h => by
    have := tailVR_sepRest vs (fun x hx => h x (by simp [hx]))
    simp only [tailVR, List.map_cons, List.flatten_cons, sepRest] at this ⊢
    rw [VR.recd_toOc v (h v (by simp)), this]
    simp


theorem failSep (Pm : List Nat) (pre : List Rc) (os0 : List ORec) (hpre : tailB pre = sepRest os0)
    (hos0 : ∀ y ∈ os0, y.Ok) (x : VR) (hx : x.Ok) (hxm : x.m = 0) (r s : Nat) (hrs : r + 1 + s = x.w)
    (w : VR) (hw : w.Ok) (hwm : w.m = 0) (ws : List VR) (hws : ∀ y ∈ ws, y.Ok) (hwsm : ∀ y ∈ ws, y.m = 0)
    (acc2 E2 : List Nat) (hacc : BitsD acc2) (hE2 : BitsD E2) (hl1 : acc2.length = w.w) (hl2 : E2.length = w.E.length) :
    ∃ os : List ORec, (∀ y ∈ os, y.Ok) ∧ os.map ORec.dgO = os0.map ORec.dgO ++ x.dg :: w.dg :: ws.map VR.dg ∧
      Pm ++ tailB (pre ++ [x.done r s]) ++ [1, 1, 3, w.O, w.P, 1] ++
        (acc2 ++ 1 :: (E2 ++ 1 :: (w.b ++ 1 :: (w.u ++ tailVR ws)))) = Pm ++ sepRest os := by
  let w' : ORec := ⟨3, w.O, w.P, acc2, E2, w.n, w.n + 1 + w.s, w.a, w.c + 1, w.t⟩
  have hw'ok : w'.Ok := by
    refine { hF := ?_, acc := hacc, E := hE2, d := by simp [w'], k := by simp [w'], Elen := ?_, Elw := ?_ }
    · have h2 := hw.O; have h3 := hw.P
      simp at h2 h3
      simp [w']; omega
    · show 2 ≤ E2.length
      rw [hl2]; exact hw.Elen
    · show E2.length = acc2.length
      rw [hl1, hl2]; exact hw.Elw
  refine ⟨os0 ++ x.toO r s :: w' :: ws.map VR.toOc, ?_, ?_, ?_⟩
  · intro y hy
    simp only [List.mem_append, List.mem_cons, List.mem_map] at hy
    rcases hy with hy | rfl | rfl | ⟨v, hv, rfl⟩
    · exact hos0 y hy
    · exact toO_ok x hx r s hrs
    · exact hw'ok
    · exact VR.toOc_ok v (hws v hv)
  · simp only [List.map_append, List.map_cons, List.map_map]
    have e1 := toO_dgO x r s hrs
    have e2 : w'.dgO = w.dg := by simp [w', ORec.dgO, VR.dg, hl1]; omega
    have e3 : ws.map (ORec.dgO ∘ VR.toOc) = ws.map VR.dg :=
      List.map_congr_left (fun v hv => VR.toOc_dg v (hws v hv))
    rw [e1, e2, e3]
  · have hb : w.b = therm w.n (w.n + 1 + w.s) := by simp [VR.b, therm, hwm]
    have hu : w.u = winStr w.a (w.c + 1) w.t := by simp [VR.u, winStr]
    rw [tailVR_sepRest ws hwsm, tailB_append]
    simp only [tailB, List.append_nil, hpre, sepRest_append, sepRest, List.append_assoc, List.cons_append,
      List.nil_append, VR.done_body_toO x hx hxm r s, ORec.tape, w', hb, hu]


theorem sNext_sum (p : Nat × Nat) (hp : 1 ≤ p.2) : (sNext p).1 + (sNext p).2 = p.1 + p.2 := by
  unfold sNext; split <;> simp <;> omega

theorem sAdv_sum : ∀ (n : Nat) (p : Nat × Nat), 1 ≤ p.2 → (sAdv n p).1 + (sAdv n p).2 = p.1 + p.2
  | 0, p, _ => by simp [sAdv]
  | n + 1, p, hp => by
    have h1 : 1 ≤ (sNext p).2 := by unfold sNext; split <;> simp <;> omega
    have := sAdv_sum n (sNext p) h1
    simp only [sAdv]; rw [this]; exact sNext_sum p hp

theorem outP_sum (c : VR) (r : Nat) (p : Nat × Nat) (hp : 1 ≤ p.2) :
    (outP c r p).1 + (outP c r p).2 = p.1 + p.2 := by
  unfold outP; split
  · rfl
  · exact sAdv_sum _ p hp

theorem outP_pos (c : VR) (r : Nat) (p : Nat × Nat) (hp : 1 ≤ p.2) : 1 ≤ (outP c r p).2 := by
  unfold outP; split
  · exact hp
  · exact sAdv_pos _ p hp

theorem loopRun_psum : ∀ (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat), 1 ≤ p.2 →
    1 ≤ (loopRun n c vs r s p).p'.2 ∧ (loopRun n c vs r s p).p'.1 + (loopRun n c vs r s p).p'.2 = p.1 + p.2
  | 0, c, vs, r, s, p, hp => by simp [loopRun, hp]
  | n + 1, c, vs, r, s, p, hp => by
    unfold loopRun
    split
    · simp [hp]
    · rename_i w ws hw
      have := loopRun_psum n w.curG (ws.map VR.dec) (w.k - 1) (w.w - w.k) (outP c r p) (outP_pos c r p hp)
      simp only
      exact ⟨this.1, by rw [this.2]; exact outP_sum c r p hp⟩

theorem passLoopF (Wf : List Nat) (hW : BitsD Wf) (P2 : List Nat) (hP2 : GoodW (1 :: P2)) :
    ∀ (n : Nat) (vs : List VR) (c : VR) (pre : List Rc) (p : Nat × Nat) (r s : Nat) (os0 : List ORec)
      (D : List (DG)),
    vs.length = n → CurInv c → (∀ x ∈ vs, x.Ok) → OutM vs → (∀ x ∈ vs, EF x) → PreOk pre → 1 ≤ p.2 →
    r + 1 + s = c.w → c.m = 0 → (∀ x ∈ vs, x.m = 0) → tailB pre = sepRest os0 → (∀ y ∈ os0, y.Ok) →
    os0.map ORec.dgO ++ (c :: vs).map VR.dg = D → ¬ PassCmp n r vs →
    ∃ (L R : List Nat) (os : List ORec) (p' : Nat × Nat), (∀ y ∈ os, y.Ok) ∧ os.map ORec.dgO = D ∧ 1 ≤ p'.2 ∧
      p'.1 + p'.2 = p.1 + p.2 ∧
      znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: P2)) pre c 0 r s vs) [])
        (hd QNTT.ODL L R) ∧
      L ++ R = (Wf ++ 1 :: (List.replicate p'.1 2 ++ List.replicate p'.2 3 ++ 1 :: P2)) ++ sepRest os := by
  intro n
  induction n with
  | zero =>
    intro vs c pre p r s os0 D _ _ _ _ _ _ _ _ _ _ _ _ _ hcmp
    exact absurd trivial (by simpa [PassCmp] using hcmp)
  | succ n ih =>
    intro vs c pre p r s os0 D hlen hc hvs hom hEF hpre hp hrs hcm hvm hpos hos0 hD hcmp
    obtain ⟨hcOk, hF, hOut⟩ := hc
    have hlen' := stepN_length r vs
    obtain ⟨w, ws, hw⟩ : ∃ w ws, stepN r vs = w :: ws := by
      cases h : stepN r vs with
      | nil => rw [h] at hlen'; simp at hlen'; omega
      | cons w ws => exact ⟨w, ws, rfl⟩
    have hok := stepN_ok r vs hvs
    rw [hw] at hok
    have hwOk : w.Ok := hok w (by simp)
    have hwsOk : ∀ x ∈ ws, x.Ok := fun x hx => hok x (by simp [hx])
    have hout := stepN_outM r vs hom
    rw [hw] at hout
    have hwm : w.O = 3 → w.m = 0 := hout w (by simp)
    have hlenws : (ws.map VR.dec).length = n := by
      rw [hw] at hlen'; simp at hlen'; simp; omega
    obtain ⟨hdgs, hmz⟩ := dg_stepN_pos r vs hvm
    rw [hw] at hdgs hmz
    have hwm0 : w.m = 0 := hmz w (by simp)
    have hwsm0 : ∀ x ∈ ws, x.m = 0 := fun x hx => hmz x (by simp [hx])
    have hEFs := stepN_EF r vs hEF
    rw [hw] at hEFs
    have hPm := pm_good Wf P2 hW hP2 p hp
    have hcmp2 : ¬ ((w.O = 3 → ∃ z, 1 ≤ w.k ∧ w.E = fld (w.k + z) w.k) ∧ PassCmp n (w.k - 1) (ws.map VR.dec)) := by
      simpa [PassCmp, hw] using hcmp
    by_cases hh : (w.O = 3 → ∃ z, 1 ≤ w.k ∧ w.E = fld (w.k + z) w.k)
    · -- compare succeeds: continue
      have hcmp3 : ¬ PassCmp n (w.k - 1) (ws.map VR.dec) := fun h => hcmp2 ⟨hh, h⟩
      have hinv := curG_inv w hwOk hwm
      have hwsOk' : ∀ x ∈ ws.map VR.dec, x.Ok := by
        intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx; exact y.dec_ok (hwsOk y hy)
      have homws : OutM (ws.map VR.dec) := dec_outM ws (fun x hx => hout x (by simp [hx]))
      have hkw := curG_kw w
      have hk1 := hwOk.k1; have hkw' := hwOk.kw
      have hrs' : w.k - 1 + 1 + (w.w - w.k) = w.curG.w := by rw [hkw.2]; omega
      have hm' : w.curG.m = 0 := curG_m0 w hwm0
      have hvm' : ∀ x ∈ ws.map VR.dec, x.m = 0 := by
        intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx; exact dec_m0 y (hwsm0 y hy)
      have hdgE : (w.curG :: ws.map VR.dec).map VR.dg = (w :: ws).map VR.dg := by
        simp only [List.map_cons, List.map_map]
        rw [(dg_curG w).1]
        congr 1
        exact List.map_congr_left (fun y _ => (dg_dec y).1)
      by_cases hO : c.O = 2
      · have h1 := colStepN c hcOk hF hO _ hPm pre hpre r s vs hvs w ws hw hh
        have hpo := preOk_done pre hpre c hcOk r s
        have hos' : tailB (pre ++ [c.done r s]) = sepRest (os0 ++ [c.toO r s]) := by
          rw [tailB_append, sepRest_append]
          simp only [tailB, sepRest, List.append_nil, hpos, VR.done_body_toO c hcOk hcm r s]
        have hD' : (os0 ++ [c.toO r s]).map ORec.dgO ++ (w.curG :: ws.map VR.dec).map VR.dg = D := by
          rw [hdgE, hdgs, ← hD, List.map_append, List.map_cons, List.map_nil, toO_dgO c r s hrs]
          simp
        obtain ⟨L, R, os, p', k1, k2, k3, ks, k4, k5⟩ :=
          ih (ws.map VR.dec) w.curG (pre ++ [c.done r s]) p (w.k - 1) (w.w - w.k) (os0 ++ [c.toO r s]) D hlenws hinv
            hwsOk' homws (dec_EF ws (fun x hx => hEFs x (by simp [hx]))) hpo hp hrs' hm' hvm' hos'
            (by intro y hy; simp only [List.mem_append, List.mem_singleton] at hy
                rcases hy with hy | rfl
                · exact hos0 y hy
                · exact toO_ok c hcOk r s hrs) hD' hcmp3
        exact ⟨L, R, os, p', k1, k2, k3, ks, h1.trans k4, k5⟩
      · have hO3 : c.O = 3 := by have := hcOk.O; simp at this; omega
        obtain ⟨hm, e, he, hew, hE⟩ := hOut hO3
        have hElen := hcOk.Elen
        have h1 := colStepO c.n c hcOk hF hO3 hm rfl Wf hW P2 hP2 pre hpre s c.E.length hElen r p e hp he hew hE vs hvs w ws
          hw hh
        have hb := eAdv_bounds c.E.length (r * c.n) e he hew
        have hc' : ({ c with E := fld c.E.length (eAdv c.E.length (r * c.n) e) } : VR).Ok :=
          { F := hcOk.F, O := hcOk.O, P := hcOk.P, k1 := hcOk.k1, kw := hcOk.kw, E := fld_bits _ _,
            Elen := by show 2 ≤ (fld c.E.length (eAdv c.E.length (r * c.n) e)).length; rw [fld_len _ _ hb.2]; exact hElen,
            Elw := by show (fld c.E.length (eAdv c.E.length (r * c.n) e)).length = _; rw [fld_len _ _ hb.2]; exact hcOk.Elw }
        have hpo := preOk_done pre hpre _ hc' r s
        have hrs'' : r + 1 + s = ({ c with E := fld c.E.length (eAdv c.E.length (r * c.n) e) } : VR).w := hrs
        have hcm' : ({ c with E := fld c.E.length (eAdv c.E.length (r * c.n) e) } : VR).m = 0 := hcm
        have hos' : tailB (pre ++ [({ c with E := fld c.E.length (eAdv c.E.length (r * c.n) e) } : VR).done r s]) =
            sepRest (os0 ++ [({ c with E := fld c.E.length (eAdv c.E.length (r * c.n) e) } : VR).toO r s]) := by
          rw [tailB_append, sepRest_append]
          simp only [tailB, sepRest, List.append_nil, hpos, VR.done_body_toO _ hc' hcm' r s]
        have hD' : (os0 ++ [({ c with E := fld c.E.length (eAdv c.E.length (r * c.n) e) } : VR).toO r s]).map ORec.dgO ++
            (w.curG :: ws.map VR.dec).map VR.dg = D := by
          rw [hdgE, hdgs, ← hD, List.map_append, List.map_cons, List.map_nil, toO_dgO _ r s hrs'']
          simp [VR.dg]
        obtain ⟨L, R, os, p', k1, k2, k3, ks, k4, k5⟩ :=
          ih (ws.map VR.dec) w.curG _ (sAdv (r * c.n) p) (w.k - 1) (w.w - w.k) _ D hlenws hinv
            hwsOk' homws (dec_EF ws (fun x hx => hEFs x (by simp [hx]))) hpo (sAdv_pos _ p hp) hrs' hm' hvm' hos'
            (by intro y hy; simp only [List.mem_append, List.mem_singleton] at hy
                rcases hy with hy | rfl
                · exact hos0 y hy
                · exact toO_ok _ hc' r s hrs'') hD' hcmp3
        exact ⟨L, R, os, p', k1, k2, k3, ks.trans (sAdv_sum _ p hp), h1.trans k4, k5⟩
    · -- compare fails now
      have hwO : w.O = 3 := Classical.byContradiction fun h => hh (fun h' => absurd h' h)
      obtain ⟨e, z, he, hE, hne⟩ := EF_mismatch w hwOk (hEFs w (by simp)) hwO hh
      by_cases hO : c.O = 2
      · obtain ⟨L, R, a2, E2, k1, k2, k3, k4, hr, hLR⟩ :=
          colStepNF c hcOk hF hO _ hPm pre hpre r s vs hvs w ws hw hwO e z he hE hne
        obtain ⟨os, hos, hdos, hT⟩ := failSep _ pre os0 hpos hos0 c hcOk hcm r s hrs w hwOk hwm0 ws hwsOk hwsm0 a2 E2 k1 k2 k3 k4
        refine ⟨L, R, os, p, hos, ?_, hp, rfl, hr, ?_⟩
        · rw [hdos, ← hD, List.map_cons, ← hdgs]; simp
        · rw [hLR, hT]
      · have hO3 : c.O = 3 := by have := hcOk.O; simp at this; omega
        obtain ⟨hm, e0, he0, hew, hE0⟩ := hOut hO3
        have hElen := hcOk.Elen
        have hb := eAdv_bounds c.E.length (r * c.n) e0 he0 hew
        have hc' : ({ c with E := fld c.E.length (eAdv c.E.length (r * c.n) e0) } : VR).Ok :=
          { F := hcOk.F, O := hcOk.O, P := hcOk.P, k1 := hcOk.k1, kw := hcOk.kw, E := fld_bits _ _,
            Elen := by show 2 ≤ (fld c.E.length (eAdv c.E.length (r * c.n) e0)).length; rw [fld_len _ _ hb.2]; exact hElen,
            Elw := by show (fld c.E.length (eAdv c.E.length (r * c.n) e0)).length = _; rw [fld_len _ _ hb.2]; exact hcOk.Elw }
        have hrs'' : r + 1 + s = ({ c with E := fld c.E.length (eAdv c.E.length (r * c.n) e0) } : VR).w := hrs
        have hcm' : ({ c with E := fld c.E.length (eAdv c.E.length (r * c.n) e0) } : VR).m = 0 := hcm
        obtain ⟨L, R, a2, E2, k1, k2, k3, k4, hr, hLR⟩ :=
          colStepOF c.n c hcOk hF hO3 hm rfl Wf hW P2 hP2 pre hpre s c.E.length hElen r p e0 hp he0 hew hE0 vs hvs w ws hw
            hwO e z he hE hne
        obtain ⟨os, hos, hdos, hT⟩ := failSep _ pre os0 hpos hos0 _ hc' hcm' r s hrs'' w hwOk hwm0 ws hwsOk hwsm0 a2 E2 k1 k2 k3 k4
        refine ⟨L, R, os, sAdv (r * c.n) p, hos, ?_, sAdv_pos _ p hp, sAdv_sum _ p hp, hr, ?_⟩
        · rw [hdos, ← hD, List.map_cons, ← hdgs]; simp [VR.dg]
        · rw [hLR, hT]


theorem outRec_EF (c : VR) (hc : CurInv c) (r : Nat) : EF (outRec c r) := by
  intro h3
  unfold outRec at h3 ⊢
  by_cases h2 : c.O = 2
  · simp [h2] at h3
  · have hO3 : c.O = 3 := by have := hc.1.O; simp at this; omega
    obtain ⟨_, e, he1, he2, hE⟩ := hc.2.2 hO3
    simp only [h2, if_false] at h3 ⊢
    have hc3 : c.E.count 3 = e := by rw [hE, count3_fld _ _ he2]
    have hb := eAdv_bounds c.E.length (r * c.n) e he1 he2
    rw [hc3]
    have hl : (fld c.E.length (eAdv c.E.length (r * c.n) e)).length = c.E.length := fld_len _ _ hb.2
    exact ⟨eAdv c.E.length (r * c.n) e, hb.1, by simp only [hl]; exact hb.2, by simp only [hl]⟩

theorem loopRun_EF : ∀ (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat),
    CurInv c → (∀ x ∈ vs, x.Ok) → OutM vs → vs.length = n →
    (∀ t ∈ (loopRun n c vs r s p).cs, EF t.1) ∧
    EF (outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r') := by
  intro n
  induction n with
  | zero =>
    intro c vs r s p hc hvs hom hl
    simp only [loopRun]
    exact ⟨by simp, outRec_EF c hc r⟩
  | succ n ih =>
    intro c vs r s p hc hvs hom hl
    have hlen' := stepN_length r vs
    obtain ⟨w, ws, hw⟩ : ∃ w ws, stepN r vs = w :: ws := by
      cases h : stepN r vs with
      | nil => rw [h] at hlen'; simp at hlen'; omega
      | cons w ws => exact ⟨w, ws, rfl⟩
    have hok := stepN_ok r vs hvs
    rw [hw] at hok
    have hwOk : w.Ok := hok w (by simp)
    have hout := stepN_outM r vs hom
    rw [hw] at hout
    have hwm : w.O = 3 → w.m = 0 := hout w (by simp)
    have hwsOk' : ∀ x ∈ ws.map VR.dec, x.Ok := by
      intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
      exact y.dec_ok (hok y (by simp [hy]))
    have homws : OutM (ws.map VR.dec) := dec_outM ws (fun x hx => hout x (by simp [hx]))
    have hlenws : (ws.map VR.dec).length = n := by
      rw [hw] at hlen'; simp at hlen'; simp; omega
    have ih' := ih w.curG (ws.map VR.dec) (w.k - 1) (w.w - w.k) (outP c r p) (curG_inv w hwOk hwm) hwsOk' homws hlenws
    simp only [loopRun, hw]
    refine ⟨?_, ih'.2⟩
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact outRec_EF c hc r
    · exact ih'.1 t ht


theorem faGF (L Pm : List Nat) (hL : NoB L) (hP : GoodW Pm) (w : VR) (hw : w.Ok) (ws : List VR)
    (hws : ∀ x ∈ ws, x.Ok) (hwO : w.O = 3) (e z : Nat) (he : 1 ≤ e) (hE : w.E = fld (e + z) e) (hne : e ≠ w.k)
    (hLe : L = Pm ++ 1 :: 1 :: ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws))) :
    ∃ (L' R' acc2 E2 : List Nat), BitsD acc2 ∧ BitsD E2 ∧ acc2.length = w.w ∧ E2.length = w.E.length ∧
      znttLogic.Reach (hd QNTT.FAL L []) (hd QNTT.ODL L' R') ∧
      L' ++ R' = Pm ++ [1, 1, 3, w.O, w.P, 1] ++ (acc2 ++ 1 :: (E2 ++ 1 :: (w.b ++ 1 :: (w.u ++ tailVR ws)))) := by
  have sPm := hP.sym4
  have sMM : Sym4 (Pm ++ [1, 1]) := sPm.app (sym4_M (sym4_M Sym4.nil))
  have sB : Sym4 ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws)) :=
    hw.hdr3.sym4.app (sym4_M (hw.tl_sym4.app (tailVR_sym4 ws hws)))
  have h1 := falScan L [] hL Sym4.nil
  rw [hLe] at h1
  have h2 := fasGood hP [] (1 :: 1 :: ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws))) Sym4.nil (sym4_M (sym4_M sB))
  have h3 := fasMM Pm ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws)) sPm sB
  obtain ⟨L', R', a2, E2, k1, k2, k3, k4, h4, hLR⟩ := fa0GFail (Pm ++ [1, 1]) w hw ws hws sMM hwO e z he hE hne
  refine ⟨L', R', a2, E2, k1, k2, k3, k4, ?_, ?_⟩
  · simp only [List.append_nil, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 h4 ⊢
    rw [hLe]
    simp only [List.append_nil, List.append_assoc, List.cons_append, List.nil_append]
    exact h1.trans (h2.trans (h3.trans h4))
  · rw [hLR]; simp

theorem failSep' (Pm : List Nat) (w : VR) (hw : w.Ok) (hwm : w.m = 0) (ws : List VR) (hws : ∀ y ∈ ws, y.Ok)
    (hwsm : ∀ y ∈ ws, y.m = 0) (acc2 E2 : List Nat) (hacc : BitsD acc2) (hE2 : BitsD E2) (hl1 : acc2.length = w.w)
    (hl2 : E2.length = w.E.length) :
    ∃ os : List ORec, (∀ y ∈ os, y.Ok) ∧ os.map ORec.dgO = w.dg :: ws.map VR.dg ∧
      Pm ++ [1, 1, 3, w.O, w.P, 1] ++ (acc2 ++ 1 :: (E2 ++ 1 :: (w.b ++ 1 :: (w.u ++ tailVR ws)))) = Pm ++ sepRest os := by
  let w' : ORec := ⟨3, w.O, w.P, acc2, E2, w.n, w.n + 1 + w.s, w.a, w.c + 1, w.t⟩
  have hw'ok : w'.Ok := by
    refine { hF := ?_, acc := hacc, E := hE2, d := by simp [w'], k := by simp [w'], Elen := ?_, Elw := ?_ }
    · have h2 := hw.O; have h3 := hw.P
      simp at h2 h3
      simp [w']; omega
    · show 2 ≤ E2.length
      rw [hl2]; exact hw.Elen
    · show E2.length = acc2.length
      rw [hl1, hl2]; exact hw.Elw
  refine ⟨w' :: ws.map VR.toOc, ?_, ?_, ?_⟩
  · intro y hy
    simp only [List.mem_cons, List.mem_map] at hy
    rcases hy with rfl | ⟨v, hv, rfl⟩
    · exact hw'ok
    · exact VR.toOc_ok v (hws v hv)
  · have e2 : w'.dgO = w.dg := by simp [w', ORec.dgO, VR.dg, hl1]; omega
    have e3 : ws.map (ORec.dgO ∘ VR.toOc) = ws.map VR.dg :=
      List.map_congr_left (fun v hv => VR.toOc_dg v (hws v hv))
    simp only [List.map_cons, List.map_map]
    rw [e2, e3]
  · have hb : w.b = therm w.n (w.n + 1 + w.s) := by simp [VR.b, therm, hwm]
    have hu : w.u = winStr w.a (w.c + 1) w.t := by simp [VR.u, winStr]
    rw [tailVR_sepRest ws hwsm]
    simp only [sepRest, List.append_assoc, List.cons_append, List.nil_append, ORec.tape, w', hb, hu]

theorem faNextF (Pm : List Nat) (hP : GoodW Pm) (t0 : (VR × Nat × Nat) × Nat) (ts : List ((VR × Nat × Nat) × Nat))
    (h : ∀ p ∈ t0 :: ts, p.1.1.Ok ∧ p.1.2.1 + 1 + p.1.2.2 = p.1.1.w ∧ 2 ≤ p.1.1.w ∧ p.2 ∈ [2, 3])
    (hm : ∀ p ∈ t0 :: ts, p.1.1.m = 0)
    (hwO : (t0.1.1.nextPass t0.2).O = 3) (e z : Nat) (he : 1 ≤ e) (hE : (t0.1.1.nextPass t0.2).E = fld (e + z) e)
    (hne : e ≠ (t0.1.1.nextPass t0.2).k) :
    ∃ (L' R' : List Nat) (os : List ORec), (∀ y ∈ os, y.Ok) ∧
      os.map ORec.dgO = (t0 :: ts).map (fun q => q.1.1.dg) ∧
      znttLogic.Reach
        (hd QNTT.FAL (Pm ++ [1, 1] ++ (t0.1.1.doneX t0.1.2.1 t0.1.2.2 t0.2).ps.body ++
          tailP (ts.map fun p => p.1.1.doneX p.1.2.1 p.1.2.2 p.2)) [])
        (hd QNTT.ODL L' R') ∧ L' ++ R' = Pm ++ sepRest os := by
  have h0 := h t0 (by simp)
  have hws : ∀ x ∈ ts.map (fun p => p.1.1.nextPass p.2), x.Ok := by
    intro x hx; simp only [List.mem_map] at hx; obtain ⟨p, hp, rfl⟩ := hx
    have := h p (by simp [hp]); exact VR.nextPass_ok _ this.1 _ this.2.2.2 this.2.2.1
  have hw := VR.nextPass_ok _ h0.1 _ h0.2.2.2 h0.2.2.1
  have hwsm : ∀ x ∈ ts.map (fun p => p.1.1.nextPass p.2), x.m = 0 := by
    intro x hx; simp only [List.mem_map] at hx; obtain ⟨p, hp, rfl⟩ := hx
    simpa [VR.nextPass] using hm p (by simp [hp])
  have hwm : (t0.1.1.nextPass t0.2).m = 0 := by simpa [VR.nextPass] using hm t0 (by simp)
  have e1 := done_ps_vr t0.1.1 h0.1 t0.1.2.1 t0.1.2.2 t0.2 h0.2.1 h0.2.2.1 h0.2.2.2
  have e2 := tailVR_doneX ts (fun p hp => h p (by simp [hp]))
  have hLe : Pm ++ 1 :: 1 :: ([(t0.1.1.nextPass t0.2).F, (t0.1.1.nextPass t0.2).O, (t0.1.1.nextPass t0.2).P] ++
      1 :: ((t0.1.1.nextPass t0.2).tl ++ tailVR (ts.map fun p => p.1.1.nextPass p.2))) =
      Pm ++ [1, 1] ++ (t0.1.1.doneX t0.1.2.1 t0.1.2.2 t0.2).ps.body ++
        tailP (ts.map fun p => p.1.1.doneX p.1.2.1 p.1.2.2 p.2) := by
    rw [e2]
    have := congrArg (fun l => Pm ++ l ++ tailVR (ts.map fun p => p.1.1.nextPass p.2)) e1
    simp only [VR.recd, List.append_assoc, List.cons_append, List.nil_append] at this ⊢
    simpa using this.symm
  have hL : NoB (Pm ++ 1 :: 1 :: ([(t0.1.1.nextPass t0.2).F, (t0.1.1.nextPass t0.2).O, (t0.1.1.nextPass t0.2).P] ++
      1 :: ((t0.1.1.nextPass t0.2).tl ++ tailVR (ts.map fun p => p.1.1.nextPass p.2)))) := by
    have := NoB_app_iff.2 ⟨hP.noB, NoB_app_iff.2 ⟨hw.recd_noB, tailVR_noB _ hws⟩⟩
    simpa [VR.recd, List.append_assoc] using this
  rw [← hLe]
  obtain ⟨L', R', a2, E2, k1, k2, k3, k4, hr, hLR⟩ := faGF _ Pm hL hP _ hw _ hws hwO e z he hE hne rfl
  have hn : ∀ x ∈ ts.map (fun p => p.1.1.nextPass p.2), x.m = 0 := hwsm
  obtain ⟨os, hos, hdos, hT⟩ := failSep' Pm (t0.1.1.nextPass t0.2) hw hwm _ hws hwsm a2 E2 k1 k2 k3 k4
  refine ⟨L', R', os, hos, ?_, hr, by rw [hLR, hT]⟩
  rw [hdos]
  simp [dg_nextPass, List.map_map, Function.comp_def]


theorem odOutF (D : List (DG)) (Wf Qp : List Nat) (hW : BitsD Wf) (m b : Nat) (p' : Nat × Nat)
    (hp : 1 ≤ p'.2) (hG : GoodW (1 :: (Qp ++ NnTail m b))) (os : List ORec) (hos : ∀ y ∈ os, y.Ok) (hne : os ≠ [])
    (hD : os.map ORec.dgO = D) (P : Nat) (hP : p'.1 + p'.2 = P) :
    OdOut' D Wf Qp (m + 1 + b) P
      ((Wf ++ 1 :: (List.replicate p'.1 2 ++ List.replicate p'.2 3 ++ 1 :: (Qp ++ NnTail m b))) ++ sepRest os) := by
  obtain ⟨o, os', rfl⟩ := List.exists_cons_of_ne_nil hne
  have hg := pm_good Wf (Qp ++ NnTail m b) hW hG p' hp
  refine ⟨List.replicate p'.1 2 ++ List.replicate p'.2 3, m + 1, b, o, os',
    bd_app (BitsD.rep _ 2 (by simp)) (BitsD.rep _ 3 (by simp)), ?_, by simp [hP], rfl, by omega, ?_, hos, hD, ?_⟩
  · obtain ⟨q, hq⟩ : ∃ q, p'.2 = q + 1 := ⟨p'.2 - 1, by omega⟩
    simp [hq, List.replicate_succ]
  · simpa [NnTail, List.append_assoc] using hg
  · simp [NnTail, List.append_assoc]


/-- One non-final pass followed by the start of the next: either refuted (`ODL`) or the next pass's first cursor
with all invariants of the next pass. -/
theorem passStepF (Wf : List Nat) (hW : BitsD Wf) (Q : List Nat) (a b : Nat)
    (hP2 : GoodW (1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
    (n : Nat) (vs : List VR) (c : VR) (p : Nat × Nat) (r s : Nat)
    (hrs : r + 1 + s = c.w) (hlen : vs.length = n) (hc : CurInv c) (hvs : ∀ x ∈ vs, x.Ok) (hom : OutM vs)
    (hp : 1 ≤ p.2) (hcmp : PassCmp n r vs) (hcw : 2 ≤ c.w) (hvw : ∀ x ∈ vs, 2 ≤ x.w)
    (hm0 : c.m = 0) (hvm : ∀ x ∈ vs, x.m = 0)
    (j y : Nat) (l' : List Nat) (hfl : c.P :: vs.map VR.P = List.replicate j 2 ++ 3 :: y :: l')
    (hEFv : ∀ x ∈ vs, EF x) :
    (∀ t ∈ ((loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
        (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]), t.1.Ok ∧ t.1.m = 0 ∧ t.2.1 + 1 + t.2.2 = t.1.w) ∧ ((∃ k q, (outP (loopRun n c vs r s p).c' (loopRun n c vs r s p).r' (loopRun n c vs r s p).p') = (k + 1, q) ∧ znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
          [] c 0 r s vs) [])
        (hd QNTT.ODL (Wf ++ [1]) (2 :: (List.replicate k 2 ++ List.replicate q 3 ++
          1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: (List.replicate b 2 ++
            tailB (((loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
              (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]).map fun t => t.1.done t.2.1 t.2.2))))))) ∨
    (∃ (q : Nat) (t0 : (VR × Nat × Nat) × Nat) (ts : List ((VR × Nat × Nat) × Nat)), 1 ≤ q ∧ q = (outP (loopRun n c vs r s p).c' (loopRun n c vs r s p).r' (loopRun n c vs r s p).p').2 ∧ (outP (loopRun n c vs r s p).c' (loopRun n c vs r s p).r' (loopRun n c vs r s p).p').1 = 0 ∧ ((t0.1.1.nextPass t0.2).O = 3 → ∃ z, 1 ≤ (t0.1.1.nextPass t0.2).k ∧ (t0.1.1.nextPass t0.2).E = fld ((t0.1.1.nextPass t0.2).k + z) (t0.1.1.nextPass t0.2).k) ∧
      (((loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
        (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]).zip (List.replicate (j + 1) 2 ++ 3 :: l')) = t0 :: ts ∧
      znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
          [] c 0 r s vs) [])
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate 0 2 ++ List.replicate q 3 ++ 1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2)))
          [] (nxtC t0) 0 (nxtR t0) (nxtS t0) (nxtVs ts)) []) ∧
      nxtR t0 + 1 + nxtS t0 = (nxtC t0).w ∧ (nxtVs ts).length = n ∧ CurInv (nxtC t0) ∧ (∀ x ∈ nxtVs ts, x.Ok) ∧ OutM (nxtVs ts) ∧
      2 ≤ (nxtC t0).w ∧ (∀ x ∈ nxtVs ts, 2 ≤ x.w) ∧ (nxtC t0).m = 0 ∧ (∀ x ∈ nxtVs ts, x.m = 0) ∧
      (nxtC t0).P :: (nxtVs ts).map VR.P = List.replicate (j + 1) 2 ++ 3 :: l') ∨
    (∃ (q : Nat) (L' R' : List Nat) (os : List ORec), 1 ≤ q ∧ q = (outP (loopRun n c vs r s p).c' (loopRun n c vs r s p).r' (loopRun n c vs r s p).p').2 ∧ (∃ (t0 : (VR × Nat × Nat) × Nat) (ts : List ((VR × Nat × Nat) × Nat)), (outP (loopRun n c vs r s p).c' (loopRun n c vs r s p).r' (loopRun n c vs r s p).p').1 = 0 ∧ (((loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r', (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]).zip (List.replicate (j + 1) 2 ++ 3 :: l')) = t0 :: ts ∧ ¬ ((t0.1.1.nextPass t0.2).O = 3 → ∃ z, 1 ≤ (t0.1.1.nextPass t0.2).k ∧ (t0.1.1.nextPass t0.2).E = fld ((t0.1.1.nextPass t0.2).k + z) (t0.1.1.nextPass t0.2).k)) ∧ (∀ y ∈ os, y.Ok) ∧
      os.map ORec.dgO = (((loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
        (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]).map fun t => t.1.dg) ∧
      znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
          [] c 0 r s vs) [])
        (hd QNTT.ODL L' R') ∧
      L' ++ R' = (Wf ++ 1 :: (List.replicate 0 2 ++ List.replicate q 3 ++ 1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2))) ++
        sepRest os)) := by
  obtain ⟨p', cs, hp', hcs, hPc, hLo, hcyc⟩ := passCycle Wf hW Q a b hP2 n vs c p r s hrs hlen hc hvs hom hp hcmp hcw hvw j y l' hfl
  obtain ⟨lo, hlo, hcsEq, hpEq⟩ := hLo
  rw [hlo, ← hcsEq]
  have hMz : ∀ t ∈ cs, t.1.O = 3 → t.1.m = 0 := by
    have hm := loopRun_m n c vs r s p hc hvs hom hlen
    rw [hlo] at hm
    intro t ht
    rw [hcsEq] at ht
    simp only [List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact hm.1 t ht
    · intro h3
      rw [(outRec_m lo.c' lo.r').2] at h3
      rw [(outRec_m lo.c' lo.r').1]
      exact hm.2 h3
  have hxs : ∀ x ∈ List.replicate (j + 1) 2 ++ 3 :: l', x ∈ [2, 3] := by
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.mem_replicate] at hx
    rcases hx with ⟨_, rfl⟩ | rfl | hx
    · simp
    · simp
    · have h1 : x ∈ c.P :: vs.map VR.P := by rw [hfl]; simp [hx]
      simp only [List.mem_cons, List.mem_map] at h1
      rcases h1 with rfl | ⟨v, hv, rfl⟩
      · exact hc.1.P
      · exact (hvs v hv).P
  have hmzs : ∀ t ∈ cs, t.1.m = 0 := by
    have hm := loopRun_m0 n c vs r s p hm0 hvm hlen
    rw [hlo] at hm
    intro t ht
    rw [hcsEq] at ht
    simp only [List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact hm.1 t ht
    · rw [(outRec_m lo.c' lo.r').1]; exact hm.2
  refine ⟨fun t ht => ⟨(hcs t ht).1, hmzs t ht, (hcs t ht).2.1⟩, ?_⟩
  rcases hcyc with ⟨hk, t0, ts, hz, hfal⟩ | ⟨k, hk, hodl⟩
  · right
    have hzl : (cs.zip (List.replicate (j + 1) 2 ++ 3 :: l')).length = n + 1 := by
      have h1 := congrArg List.length hPc
      have h2 := congrArg List.length hfl
      simp at h1 h2 ⊢
      omega
    rw [hz] at hzl
    simp only [List.length_cons] at hzl
    have hmem : ∀ q ∈ t0 :: ts, q ∈ cs.zip (List.replicate (j + 1) 2 ++ 3 :: l') := by
      intro q hq; rw [hz]; exact hq
    have hh : ∀ q ∈ t0 :: ts, q.1.1.Ok ∧ q.1.2.1 + 1 + q.1.2.2 = q.1.1.w ∧ 2 ≤ q.1.1.w ∧ q.2 ∈ [2, 3] := by
      intro q hq
      have := List.of_mem_zip (hmem q hq)
      have h3 := hcs q.1 this.1
      exact ⟨h3.1, h3.2.1, h3.2.2, hxs _ this.2⟩
    have h0 := hh t0 (by simp)
    have hGP := goodW_pmNext Wf hW Q a b p'.2 hP2 hp'
    by_cases hcmp0 : (t0.1.1.nextPass t0.2).O = 3 → ∃ z, 1 ≤ (t0.1.1.nextPass t0.2).k ∧
      (t0.1.1.nextPass t0.2).E = fld ((t0.1.1.nextPass t0.2).k + z) (t0.1.1.nextPass t0.2).k
    · left
      have hfn := faNext _ hGP t0 ts hh hcmp0
      have hw := VR.nextPass_ok _ h0.1 _ h0.2.2.2 h0.2.2.1
      have hmz : (t0.1.1.nextPass t0.2).O = 3 → (t0.1.1.nextPass t0.2).m = 0 := by
        intro h3
        exact hMz t0.1 (List.of_mem_zip (hmem t0 (by simp))).1 (by simpa [VR.nextPass] using h3)
      refine ⟨p'.2, t0, ts, hp', by rw [hpEq], by rw [← hpEq]; exact hk, hcmp0, hz, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals try simp only [nxtC, nxtW, nxtR, nxtS, nxtVs]
      · simp only [List.replicate_zero, List.nil_append]
        exact hfal.trans hfn
      · have := (curG_kw (t0.1.1.nextPass t0.2)).2
        have h1 := hw.k1; have h2 := hw.kw
        omega
      · simpa using hzl
      · exact curG_inv _ hw hmz
      · intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨y, ⟨q, hq, rfl⟩, rfl⟩ := hx
        have hq' := hh q (List.mem_cons_of_mem _ hq)
        exact VR.dec_ok _ (VR.nextPass_ok _ hq'.1 _ hq'.2.2.2 hq'.2.2.1)
      · apply dec_outM
        intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨q, hq, rfl⟩ := hx
        intro h3
        exact hMz q.1 (List.of_mem_zip (hmem q (List.mem_cons_of_mem _ hq))).1 (by simpa [VR.nextPass] using h3)
      · rw [(curG_kw (t0.1.1.nextPass t0.2)).2]
        simpa [VR.nextPass] using h0.2.2.1
      · intro x hx
        simp only [nxtVs, List.mem_map] at hx
        obtain ⟨y, ⟨q, hq, rfl⟩, rfl⟩ := hx
        have hq' := hh q (List.mem_cons_of_mem _ hq)
        rw [dec_w]
        simpa [VR.nextPass] using hq'.2.2.1
      · exact curG_m0 _ (by simpa [VR.nextPass] using hmzs t0.1 (List.of_mem_zip (hmem t0 (by simp))).1)
      · intro x hx
        simp only [nxtVs, List.mem_map] at hx
        obtain ⟨y, ⟨q, hq, rfl⟩, rfl⟩ := hx
        exact dec_m0 _ (by simpa [VR.nextPass] using hmzs q.1 (List.of_mem_zip (hmem q (List.mem_cons_of_mem _ hq))).1)
      · have hs : ((cs.zip (List.replicate (j + 1) 2 ++ 3 :: l')).map Prod.snd) = List.replicate (j + 1) 2 ++ 3 :: l' := by
          rw [List.map_snd_zip]
          have h1 := congrArg List.length hPc
          have h2 := congrArg List.length hfl
          simp at h1 h2 ⊢
          omega
        rw [hz] at hs
        simp only [List.map_cons] at hs
        rw [← hs]
        simp [nxtC, nxtW, nxtVs, curG_P, dec_P, VR.nextPass, Function.comp_def]
    · right
      have hwO : (t0.1.1.nextPass t0.2).O = 3 := Classical.byContradiction fun h => hcmp0 (fun h' => absurd h' h)
      have hw := VR.nextPass_ok _ h0.1 _ h0.2.2.2 h0.2.2.1
      have hEFl := loopRun_EF n c vs r s p hc hvs hom hlen
      rw [hlo] at hEFl
      have hEFcs : ∀ t ∈ cs, EF t.1 := by
        intro t ht
        rw [hcsEq] at ht
        simp only [List.mem_append, List.mem_singleton] at ht
        rcases ht with ht | rfl
        · exact hEFl.1 t ht
        · exact hEFl.2
      have hEF0 : EF (t0.1.1.nextPass t0.2) :=
        EF_of rfl rfl (hEFcs t0.1 (List.of_mem_zip (hmem t0 (by simp))).1)
      obtain ⟨e, z, he, hE, hne⟩ := EF_mismatch _ hw hEF0 hwO hcmp0
      have hmm : ∀ q ∈ t0 :: ts, q.1.1.m = 0 := fun q hq =>
        hmzs q.1 (List.of_mem_zip (hmem q hq)).1
      obtain ⟨L', R', os, hok, hdos, hr, hLR⟩ := faNextF _ hGP t0 ts hh hmm hwO e z he hE hne
      refine ⟨p'.2, L', R', os, hp', by rw [hpEq], ⟨t0, ts, by rw [← hpEq]; exact hk, hz, hcmp0⟩, hok, ?_, hfal.trans hr, ?_⟩
      · rw [hdos]
        have hcl : cs.length = n + 1 := by
          have := congrArg List.length hPc
          simp at this ⊢; omega
        have hzl2 : (List.replicate (j + 1) 2 ++ 3 :: l').length = n + 1 := by
          have := congrArg List.length hfl
          simp at this ⊢; omega
        have hmf := List.map_fst_zip (l₁ := cs) (l₂ := List.replicate (j + 1) 2 ++ 3 :: l') (by omega)
        rw [hz] at hmf
        rw [← hmf]
        simp [List.map_map, Function.comp_def]
      · rw [hLR]; simp
  · left
    exact ⟨k, p'.2, by rw [← hpEq]; exact Prod.ext hk rfl, hodl⟩




theorem nxt_EF (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat) (hc : CurInv c) (hvs : ∀ x ∈ vs, x.Ok)
    (hom : OutM vs) (hlen : vs.length = n) (L2 : List Nat) (t0 : (VR × Nat × Nat) × Nat)
    (ts : List ((VR × Nat × Nat) × Nat))
    (hz : (((loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
        (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]).zip L2) = t0 :: ts) :
    ∀ x ∈ nxtVs ts, EF x := by
  have hEFl := loopRun_EF n c vs r s p hc hvs hom hlen
  intro x hx
  simp only [nxtVs, List.mem_map] at hx
  obtain ⟨y, ⟨q, hq, rfl⟩, rfl⟩ := hx
  have hmem : q ∈ ((loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
        (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]).zip L2 := by
    rw [hz]; exact List.mem_cons_of_mem _ hq
  have hq1 := (List.of_mem_zip hmem).1
  have hEFq : EF q.1.1 := by
    simp only [List.mem_append, List.mem_singleton] at hq1
    rcases hq1 with h | h
    · exact hEFl.1 q.1 h
    · rw [h]; exact hEFl.2
  exact EF_of (dec_EO _).1 (dec_EO _).2 (EF_of rfl rfl hEFq)

theorem failA (Wf : List Nat) (hW : BitsD Wf) (Q'' : List Nat) (m b n : Nat) (vs : List VR) (c : VR) (p : Nat × Nat)
    (r s : Nat) (hP2 : GoodW (1 :: ((Q'' ++ [1]) ++ NnTail m b)))
    (hrs : r + 1 + s = c.w) (hlen : vs.length = n) (hc : CurInv c) (hvs : ∀ x ∈ vs, x.Ok) (hom : OutM vs)
    (hEF : ∀ x ∈ vs, EF x) (hp : 1 ≤ p.2) (hm0 : c.m = 0) (hvm : ∀ x ∈ vs, x.m = 0) (hnc : ¬ PassCmp n r vs) :
    ∃ L' R' : List Nat, OdOut' ((c :: vs).map VR.dg) Wf (Q'' ++ [1]) (m + 1 + b) (p.1 + p.2) (L' ++ R') ∧
      znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: ((Q'' ++ [1]) ++ NnTail m b)))
          [] c 0 r s vs) [])
        (hd QNTT.ODL L' R') := by
  obtain ⟨L, R, os, p', hok, hdos, hp', hps, hr, hLR⟩ := passLoopF Wf hW ((Q'' ++ [1]) ++ NnTail m b) hP2 n vs c [] p r s []
    ((c :: vs).map VR.dg) hlen hc hvs hom hEF (by intro x hx; simp at hx) hp hrs hm0 hvm rfl
    (by intro y hy; simp at hy) (by simp) hnc
  refine ⟨L, R, ?_, hr⟩
  rw [hLR]
  exact odOutF _ Wf (Q'' ++ [1]) hW m b p' hp' hP2 os hok (by intro h; rw [h] at hdos; simp at hdos) hdos _ hps

def passPOf (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat) : Nat × Nat :=
  outP (loopRun n c vs r s p).c' (loopRun n c vs r s p).r' (loopRun n c vs r s p).p'

/-- Full success of `m + 1` further passes: compare outcome and `S` register check of every pass. -/
def FOk : Nat → Nat → VR → List VR → Nat → Nat → Nat × Nat → Nat → List Nat → Prop
  | 0, n, c, vs, r, s, p, _, _ => PassCmp n r vs ∧ (passPOf n c vs r s p).1 ≠ 0
  | m + 1, n, c, vs, r, s, p, j, L =>
    PassCmp n r vs ∧ (passPOf n c vs r s p).1 = 0 ∧ ∀ t0 ts,
      (passCsOf n c vs r s p).zip (List.replicate (j + 1) 2 ++ 3 :: L.tail) = t0 :: ts →
      ((nxtW t0).O = 3 → ∃ z, 1 ≤ (nxtW t0).k ∧ (nxtW t0).E = fld ((nxtW t0).k + z) (nxtW t0).k) ∧
      FOk m n (nxtC t0) (nxtVs ts) (nxtR t0) (nxtS t0) (0, (passPOf n c vs r s p).2) (j + 1) L.tail

theorem FOk_succ {m n : Nat} {c : VR} {vs : List VR} {r s j : Nat} {p : Nat × Nat} {l' : List Nat} {y : Nat}
    {t0 : (VR × Nat × Nat) × Nat} {ts : List ((VR × Nat × Nat) × Nat)}
    (hc : PassCmp n r vs) (hk : (passPOf n c vs r s p).1 = 0)
    (hz : (passCsOf n c vs r s p).zip (List.replicate (j + 1) 2 ++ 3 :: l') = t0 :: ts)
    (hcm : (nxtW t0).O = 3 → ∃ z, 1 ≤ (nxtW t0).k ∧ (nxtW t0).E = fld ((nxtW t0).k + z) (nxtW t0).k)
    (hf : FOk m n (nxtC t0) (nxtVs ts) (nxtR t0) (nxtS t0) (0, (passPOf n c vs r s p).2) (j + 1) l') :
    FOk (m + 1) n c vs r s p j (y :: l') := by
  refine ⟨hc, hk, fun t0' ts' hz' => ?_⟩
  have := hz'.symm.trans hz
  obtain ⟨h1, h2⟩ := List.cons.inj this
  subst h1; subst h2
  exact ⟨hcm, hf⟩

theorem FOk_inv {m n : Nat} {c : VR} {vs : List VR} {r s j : Nat} {p : Nat × Nat} {l' : List Nat} {y : Nat}
    {t0 : (VR × Nat × Nat) × Nat} {ts : List ((VR × Nat × Nat) × Nat)}
    (h : FOk (m + 1) n c vs r s p j (y :: l'))
    (hz : (passCsOf n c vs r s p).zip (List.replicate (j + 1) 2 ++ 3 :: l') = t0 :: ts) :
    ((nxtW t0).O = 3 → ∃ z, 1 ≤ (nxtW t0).k ∧ (nxtW t0).E = fld ((nxtW t0).k + z) (nxtW t0).k) ∧
      FOk m n (nxtC t0) (nxtVs ts) (nxtR t0) (nxtS t0) (0, (passPOf n c vs r s p).2) (j + 1) l' :=
  h.2.2 t0 ts hz


theorem passPOf_sum (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat) (hp : 1 ≤ p.2) :
    1 ≤ (passPOf n c vs r s p).2 ∧ (passPOf n c vs r s p).1 + (passPOf n c vs r s p).2 = p.1 + p.2 := by
  have := loopRun_psum n c vs r s p hp
  unfold passPOf
  exact ⟨outP_pos _ _ _ this.1, by rw [outP_sum _ _ _ this.1, this.2]⟩


/-- All passes of one assignment, without the semantic hypothesis: refuted (`ODL`, parsable tape) or successful (`SU1`). -/
theorem passesRunF (Wf : List Nat) (hW : BitsD Wf) (Q'' : List Nat) :
    ∀ (m b n : Nat) (vs : List VR) (c : VR) (p : Nat × Nat) (r s j : Nat) (L : List Nat),
    GoodW (1 :: ((Q'' ++ [1]) ++ NnTail m b)) →
    r + 1 + s = c.w → vs.length = n → CurInv c → (∀ x ∈ vs, x.Ok) → OutM vs → (∀ x ∈ vs, EF x) → 1 ≤ p.2 →
    2 ≤ c.w → (∀ x ∈ vs, 2 ≤ x.w) → c.m = 0 → (∀ x ∈ vs, x.m = 0) →
    c.P :: vs.map VR.P = List.replicate j 2 ++ 3 :: L → m ≤ L.length →
    (∃ L' R' : List Nat, OdOut' ((c :: vs).map VR.dg) Wf (Q'' ++ [1]) (m + 1 + b) (p.1 + p.2) (L' ++ R') ∧
      znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: ((Q'' ++ [1]) ++ NnTail m b)))
          [] c 0 r s vs) [])
        (hd QNTT.ODL L' R') ∧ ¬ FOk m n c vs r s p j L) ∨
    (∃ T, SuOut ((c :: vs).map VR.dg) Wf Q'' (b + m + 1) T ∧
      znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: ((Q'' ++ [1]) ++ NnTail m b)))
          [] c 0 r s vs) [])
        (hdR QNTT.SU1 [] T) ∧ FOk m n c vs r s p j L) := by
  intro m
  induction m with
  | zero =>
    intro b n vs c p r s j L hP2 hrs hlen hc hvs hom hEF hp hcw hvw hm0 hvm hfl hL
    by_cases hcmp : PassCmp n r vs
    · have e : (Q'' ++ [1]) ++ NnTail 0 b = Q'' ++ [1] ++ [3] ++ List.replicate b 2 := by simp [NnTail]
      rw [e] at hP2 ⊢
      obtain ⟨p', cs, hp', hcs, hPc, hLo, hlast⟩ := lastCycle Wf hW Q'' b hP2 n vs c p r s hrs hlen hc hvs hom hp hcmp hcw hvw
      have hne : cs ≠ [] := by
        intro h; rw [h] at hPc; simp at hPc
      have hmzs : ∀ t ∈ cs, t.1.m = 0 := by
        obtain ⟨lo, hlo, hcsEq, hpEq⟩ := hLo
        have hm := loopRun_m0 n c vs r s p hm0 hvm hlen
        rw [hlo] at hm
        intro t ht
        rw [hcsEq] at ht
        simp only [List.mem_append, List.mem_singleton] at ht
        rcases ht with ht | rfl
        · exact hm.1 t ht
        · rw [(outRec_m lo.c' lo.r').1]; exact hm.2
      have hD : cs.map (fun t => t.1.dg) = (c :: vs).map VR.dg := by
        obtain ⟨lo, hlo, hcsEq, _⟩ := hLo
        have := dg_runAll_pos n c vs r s p hm0 hvm hlen
        rw [hlo] at this; rw [hcsEq]; exact this
      have hcs' : ∀ t ∈ cs, t.1.Ok ∧ t.1.m = 0 ∧ t.2.1 + 1 + t.2.2 = t.1.w :=
        fun t ht => ⟨(hcs t ht).1, hmzs t ht, (hcs t ht).2.1⟩
      have hP2' : GoodW (1 :: (Q'' ++ 1 :: 2 :: List.replicate b 2)) := by
        have := goodW_swap_tail (1 :: (Q'' ++ [1])).length (1 :: (Q'' ++ [1])) 3 2
          (List.replicate b 2) (List.replicate b 2) rfl (by simp) (by simp)
          (BitsD.rep b 2 (by simp)) (BitsD.rep b 2 (by simp))
          (by simpa [List.append_assoc] using hP2)
        simpa [List.append_assoc] using this
      have hpO : passPOf n c vs r s p = p' := by
        obtain ⟨lo, hlo, _, hpEq⟩ := hLo
        unfold passPOf; rw [hlo]; exact hpEq.symm
      have hsum : p'.1 + p'.2 = p.1 + p.2 := by
        have := (passPOf_sum n c vs r s p hp).2; rw [hpO] at this; exact this
      rcases hlast with ⟨k, hk, h1⟩ | ⟨hk, h1⟩
      · right
        have hu := goodW_reg Wf (List.replicate (k + 1) 2 ++ List.replicate p'.2 3) _ hW
          (bd_app (BitsD.rep _ 2 (by simp)) (BitsD.rep _ 3 (by simp)))
          (by intro h; have := congrArg List.length h; simp at this) hP2'
        obtain ⟨o, os, hok, hdg, hex⟩ := tapeOutP_ex cs hcs' hne
        refine ⟨_, ⟨List.replicate (k + 1) 2 ++ List.replicate p'.2 3, o, os,
          bd_app (BitsD.rep _ 2 (by simp)) (BitsD.rep _ 3 (by simp)), ?_, hok, hdg.trans hD, rfl⟩, ?_, hcmp, ?_⟩
        · simpa [List.replicate_succ, List.append_assoc] using hu
        · rw [hex] at h1
          simpa [List.replicate_succ, List.append_assoc] using h1
        · rw [hpO, hk]; simp
      · left
        have hu := goodW_reg Wf (List.replicate p'.2 3) _ hW (BitsD.rep _ 3 (by simp))
          (by intro h; have := congrArg List.length h; simp at this; omega) hP2'
        obtain ⟨o, os, hok, hdg, hex⟩ := tapeOutP_ex cs hcs' hne
        obtain ⟨R', hT, hr⟩ : ∃ R', OdOut ((c :: vs).map VR.dg) Wf (Q'' ++ [1]) (0 + 1 + b) (p.1 + p.2) R' ∧
            znttLogic.Reach
              (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 ::
                (Q'' ++ [1] ++ [3] ++ List.replicate b 2))) [] c 0 r s vs) [])
              (hd QNTT.ODL (Wf ++ [1]) R') := by
          refine ⟨(List.replicate p'.2 3 ++ 1 :: ((Q'' ++ [1]) ++ List.replicate 0 3 ++ 2 :: List.replicate b 2)) ++
            sepRest (o :: os), ⟨List.replicate p'.2 3, 0, b, o, os, BitsD.rep _ 3 (by simp),
            by intro h; have := congrArg List.length h; simp at this; omega, by simp; omega, by omega, ?_, hok, hdg.trans hD, ?_⟩, ?_⟩
          · simpa [List.append_assoc] using hu
          · simp [List.append_assoc]
          · rw [hex] at h1
            simpa [List.append_assoc] using h1
        exact ⟨Wf ++ [1], R', hT.to', hr, fun hF => by
          have := hF.2; rw [hpO, hk] at this; exact this rfl⟩
    · obtain ⟨L', R', h1, h2⟩ := failA Wf hW Q'' 0 b n vs c p r s hP2 hrs hlen hc hvs hom hEF hp hm0 hvm hcmp
      exact Or.inl ⟨L', R', h1, h2, fun hF => hcmp hF.1⟩
  | succ a ih =>
    intro b n vs c p r s j L hP2 hrs hlen hc hvs hom hEF hp hcw hvw hm0 hvm hfl hL
    by_cases hc1 : PassCmp n r vs
    case neg =>
      obtain ⟨L', R', h1, h2⟩ := failA Wf hW Q'' (a + 1) b n vs c p r s hP2 hrs hlen hc hvs hom hEF hp hm0 hvm hc1
      exact Or.inl ⟨L', R', h1, h2, fun hF => hc1 hF.1⟩
    obtain ⟨y, l', rfl⟩ : ∃ y l', L = y :: l' := by
      cases L with
      | nil => simp at hL
      | cons y l' => exact ⟨y, l', rfl⟩
    have e : (Q'' ++ [1]) ++ NnTail (a + 1) b = (Q'' ++ [1]) ++ List.replicate (a + 2) 3 ++ List.replicate b 2 := by
      simp [NnTail, List.append_assoc]
    rw [e] at hP2 ⊢
    have hstep := passStepF Wf hW (Q'' ++ [1]) a b hP2 n vs c p r s hrs hlen hc hvs hom hp hc1 hcw hvw hm0 hvm j y l' hfl hEF
    obtain ⟨hcsOk, hst⟩ := hstep
    have hP2'' : GoodW (1 :: ((Q'' ++ [1]) ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2)) := goodW_shiftNn _ a b hP2
    rcases hst with ⟨k, q, hSo, h1⟩ | ⟨q, t0, ts, hq, hqe, hk0, hcmpt, hz, h1, hrs1, hlen1, hc1', hvs1, hom1, hcw1, hvw1, hm1, hvm1, hfl1⟩ |
        ⟨q, L', R', os, hq, hqe3, hX3, hok, hdos, h1, hLR⟩
    · have hsumO : (k + 1) + q = p.1 + p.2 := by
        have hs := (passPOf_sum n c vs r s p hp).2
        unfold passPOf at hs; rw [hSo] at hs; exact hs
      obtain ⟨R', hO, hr⟩ : ∃ R', OdOut ((c :: vs).map VR.dg) Wf (Q'' ++ [1]) (a + 1 + 1 + b) (p.1 + p.2) R' ∧
          znttLogic.Reach
            (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 ::
              ((Q'' ++ [1]) ++ List.replicate (a + 2) 3 ++ List.replicate b 2))) [] c 0 r s vs) [])
            (hd QNTT.ODL (Wf ++ [1]) R') := by
        have hu := goodW_reg Wf (List.replicate (k + 1) 2 ++ List.replicate q 3) _ hW
          (bd_app (BitsD.rep _ 2 (by simp)) (BitsD.rep _ 3 (by simp)))
          (by intro h; have := congrArg List.length h; simp at this) (by simpa [List.append_assoc] using hP2'')
        have hne : ((loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
            (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]) ≠ [] := by simp
        obtain ⟨o, os, hok, hdg, hex⟩ := tapeOutP_ex _ hcsOk hne
        refine ⟨((2 :: List.replicate k 2) ++ List.replicate q 3 ++ 1 :: ((Q'' ++ [1]) ++ List.replicate (a + 1) 3 ++
            2 :: List.replicate b 2)) ++ sepRest (o :: os),
          ⟨(2 :: List.replicate k 2) ++ List.replicate q 3, a + 1, b, o, os,
            bd_app (BitsD.cons (by simp) (BitsD.rep _ 2 (by simp))) (BitsD.rep _ 3 (by simp)),
            by intro h; have := congrArg List.length h; simp at this, by simp; omega, by omega, ?_, hok,
            hdg.trans (dg_runAll_pos n c vs r s p hm0 hvm hlen), ?_⟩, ?_⟩
        · rw [List.replicate_succ' (n := a) (a := 3)]; simpa [List.append_assoc, List.replicate_succ] using hu
        · simp [List.append_assoc]
        · rw [hex] at h1
          rw [List.replicate_succ' (n := a) (a := 3)]; simpa [List.append_assoc, List.replicate_succ] using h1
      refine Or.inl ⟨Wf ++ [1], R', hO.to', hr, fun hF => ?_⟩
      have h0 := hF.2.1
      unfold passPOf at h0; rw [hSo] at h0; exact absurd h0 (by simp)
    · have hEFn := nxt_EF n c vs r s p hc hvs hom hlen _ t0 ts hz
      have hP2' : GoodW (1 :: ((Q'' ++ [1]) ++ NnTail a (b + 1))) := by
        rw [← nn_eq]
        simpa [List.append_assoc] using goodW_shiftNn (Q'' ++ [1]) a b hP2
      have hih := ih (b + 1) n (nxtVs ts) (nxtC t0) (0, q) (nxtR t0) (nxtS t0) (j + 1) l' hP2' hrs1 hlen1 hc1' hvs1 hom1
        hEFn hq hcw1 hvw1 hm1 hvm1 (by simpa using hfl1) (by simpa using hL)
      have e2 : (Q'' ++ [1]) ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2 = (Q'' ++ [1]) ++ NnTail a (b + 1) := by
        rw [List.append_assoc, nn_eq]
      rw [e2] at h1
      simp only [List.replicate_zero, List.nil_append] at h1 hih
      have hEq : (nxtC t0 :: nxtVs ts).map VR.dg = (c :: vs).map VR.dg := by
        have hcl : ((loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
            (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]).length = n + 1 := by
          simp [loopRun_cs_length n c vs r s p hlen]
        have hzl : (List.replicate (j + 1) 2 ++ 3 :: l').length = n + 1 := by
          have := congrArg List.length hfl
          simp at this ⊢; omega
        have hmf := List.map_fst_zip (l₁ := (loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
            (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]) (l₂ := List.replicate (j + 1) 2 ++ 3 :: l') (by omega)
        rw [hz] at hmf
        have hp := dg_runAll_pos n c vs r s p hm0 hvm hlen
        rw [← hp, ← hmf]
        simp [nxtC, nxtVs, nxtW, dg_curG, dg_nextPass, dg_dec, List.map_map, Function.comp_def]
      have hqe' : (0, q) = (0, (passPOf n c vs r s p).2) := by rw [hqe]; rfl
      have hcm : ((nxtW t0).O = 3 → ∃ z, 1 ≤ (nxtW t0).k ∧ (nxtW t0).E = fld ((nxtW t0).k + z) (nxtW t0).k) := hcmpt
      have hq0 : (0, q).1 + (0, q).2 = p.1 + p.2 := by
        have hsum := (passPOf_sum n c vs r s p hp).2
        have hk0' : (passPOf n c vs r s p).1 = 0 := hk0
        have hqe2 : q = (passPOf n c vs r s p).2 := hqe
        simp only; omega
      rcases hih with ⟨L', R', ho, hr, hnf⟩ | ⟨T, ho, hr, hf⟩
      · rw [hq0] at ho
        refine Or.inl ⟨L', R', by rw [hEq] at ho; rwa [show a + 1 + (b + 1) = a + 1 + 1 + b by omega] at ho, h1.trans hr, fun hF => hnf ?_⟩
        rw [hqe']; exact (FOk_inv hF hz).2
      · exact Or.inr ⟨T, by rw [hEq] at ho; rwa [show b + 1 + a + 1 = b + (a + 1) + 1 by omega] at ho, h1.trans hr,
          FOk_succ hc1 hk0 hz hcm (by rw [← hqe']; exact hf)⟩
    · have hP2n : GoodW (1 :: ((Q'' ++ [1]) ++ NnTail a (b + 1))) := by
        rw [← nn_eq]
        simpa [List.append_assoc] using hP2''
      have hdgE := dg_runAll_pos n c vs r s p hm0 hvm hlen
      have hne : os ≠ [] := by intro h; rw [h] at hdos; simp at hdos
      have hO := odOutF ((c :: vs).map VR.dg) Wf (Q'' ++ [1]) hW a (b + 1) (0, q) hq hP2n os hok hne (by rw [hdos, hdgE]) (p.1 + p.2) (by
        obtain ⟨t0, ts, hk3, _⟩ := hX3
        have hsum := (passPOf_sum n c vs r s p hp).2
        have hk0' : (passPOf n c vs r s p).1 = 0 := hk3
        have hqe2 : q = (passPOf n c vs r s p).2 := hqe3
        simp only; omega)
      have hnF : ¬ FOk (a + 1) n c vs r s p j (y :: l') := by
        intro hF
        obtain ⟨t0, ts, hk, hz, hn⟩ := hX3
        exact hn (FOk_inv hF hz).1
      refine Or.inl ⟨L', R', ?_, h1, hnF⟩
      rw [hLR]
      have := hO
      rw [show a + 1 + 1 + b = a + 1 + (b + 1) by omega]
      simpa [nn_eq, List.append_assoc] using this


/-- One whole assignment, `Sem`-free: the next assignment (`WI0`), the overflow (beep, restart at `PA0` with `C` grown),
or success (`SU1`, restart at `PA0`). -/
theorem assignRunF (Wf : List Nat) (hW : BitsD Wf) (Kf Cf : List Nat) (hK : BitsD Kf) (hC : BitsD Cf)
    (m b n : Nat) (vs : List VR) (c : VR) (p : Nat × Nat) (r s j : Nat) (L : List Nat)
    (hP2 : GoodW (1 :: (((Kf ++ 1 :: Cf) ++ [1]) ++ NnTail m b)))
    (hrs : r + 1 + s = c.w) (hlen : vs.length = n) (hc : CurInv c) (hvs : ∀ x ∈ vs, x.Ok) (hom : OutM vs)
    (hEF : ∀ x ∈ vs, EF x) (hp : 1 ≤ p.2)
    (hcw : 2 ≤ c.w) (hvw : ∀ x ∈ vs, 2 ≤ x.w) (hm0 : c.m = 0) (hvm : ∀ x ∈ vs, x.m = 0)
    (hfl : c.P :: vs.map VR.P = List.replicate j 2 ++ 3 :: L) (hL : m ≤ L.length) :
    let st := hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 ::
          (((Kf ++ 1 :: Cf) ++ [1]) ++ NnTail m b))) [] c 0 r s vs) []
    (∃ u v os' X R'', Rest u v ∧ ¬ FOk m n c vs r s p j L ∧ StepInfo ((c :: vs).map VR.dg) Wf Kf Cf (m + 1 + b) (p.1 + p.2) v os' ∧ X ++ 3 :: R'' = (v ++ [1, 1]) ++ tapeL os' ∧
      znttLogic.Reach st (hd QNTT.WI0 X (3 :: R''))) ∨
    (∃ (A : List Nat) (n0 : Nat), StepNone ((c :: vs).map VR.dg) ∧ ¬ FOk m n c vs r s p j L ∧ znttLogic.Reach st (hd QNTT.BEEP A []) ∧
      ∃ X, znttLogic.zstep (hd QNTT.BEEP A []) = some X ∧
        znttLogic.Reach X (hdR QNTT.PA0 [3] (1 :: (Kf.map (fun x => if x = 1 then 1 else 3) ++ 1 ::
          ((Cf.map (fun x => if x = 1 then 1 else 3) ++ [3]) ++ 1 ::
            (List.replicate (m + 1 + b) 3 ++ List.replicate (n0 + 1) 0)))))) ∨
    (∃ N : Nat, ∃ T, SuOut ((c :: vs).map VR.dg) Wf (Kf ++ 1 :: Cf) (b + m + 1) T ∧ FOk m n c vs r s p j L ∧
      znttLogic.Reach st (hdR QNTT.SU1 [] T) ∧
      znttLogic.Reach (hdR QNTT.SU1 [] T) (hdR QNTT.PA0 [3] (1 :: (Kf ++ 1 :: (Cf ++ 1 :: (List.replicate (b + m + 1 + 1) 3 ++
        List.replicate (N + 1) 0)))))) := by
  intro st
  rcases passesRunF Wf hW (Kf ++ 1 :: Cf) m b n vs c p r s j L hP2 hrs hlen hc hvs hom hEF hp hcw hvw hm0 hvm hfl hL with
    ⟨L', R', hT, hr, hnF⟩ | ⟨T, hT, hr, hF⟩
  · rcases odlNext3 _ Wf Kf Cf hW hK hC _ (p.1 + p.2) L' R' hT with ⟨u, v, os', X, R'', hv, si, e, h⟩ | ⟨A, n0, sn, hb, X, hX, hXr⟩
    · exact Or.inl ⟨u, v, os', X, R'', hv, hnF, si, e, hr.trans h⟩
    · exact Or.inr (Or.inl ⟨A, n0, sn, hnF, hr.trans hb, X, hX, hXr⟩)
  · obtain ⟨N, hN⟩ := sucRestart _ Wf Kf Cf (b + m) T hW hK hC hT
    exact Or.inr (Or.inr ⟨N, T, hT, hF, hr, hN⟩)


/-- Odometer measure on digit tuples. -/
def ph : List (DG) → Nat
  | [] => 0
  | (d, e, z, m, _) :: gs => (m * (d + e + 1) + e) + (z + 1 + m) * (d + e + 1) * ph gs

theorem ph_step1 (d e zk m : Nat) (l : Nat × Nat) (X : List (DG)) (he : 1 ≤ e) :
    ph ((d + 1, e - 1, zk, m, l) :: X) < ph ((d, e, zk, m, l) :: X) := by
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  simp only [ph, Nat.add_sub_cancel]
  have : d + 1 + e' + 1 = d + (e' + 1) + 1 := by omega
  rw [this]; omega

theorem ph_step2 (d zk m' : Nat) (l : Nat × Nat) (X : List (DG)) :
    ph ((0, d, zk + 1, m', l) :: X) < ph ((d, 0, zk, m' + 1, l) :: X) := by
  simp only [ph]
  have h1 : 0 + d + 1 = d + 0 + 1 := by omega
  have h2 : zk + 1 + 1 + m' = zk + 1 + (m' + 1) := by omega
  rw [h1, h2]
  have : m' * (d + 0 + 1) + d < (m' + 1) * (d + 0 + 1) + 0 := by
    rw [Nat.add_mul]; omega
  omega

theorem ph_step3 (d zk : Nat) (l : Nat × Nat) (X X2 : List (DG)) (h : ph X2 < ph X) :
    ph ((0, d, 0, zk, l) :: X2) < ph ((d, 0, zk, 0, l) :: X) := by
  simp only [ph]
  have h1 : 0 + d + 1 = d + 0 + 1 := by omega
  rw [h1]
  have h3 : (d + 0 + 1) * (zk + 1) * (ph X2 + 1) ≤ (d + 0 + 1) * (zk + 1) * ph X := Nat.mul_le_mul_left _ h
  have h4 : zk * (d + 0 + 1) + d < (zk + 1) * (d + 0 + 1) := by rw [Nat.add_mul]; omega
  have e1 : (0 + 1 + zk) * (d + 0 + 1) = (d + 0 + 1) * (zk + 1) := by rw [Nat.mul_comm]; congr 1; omega
  have e2 : (zk + 1 + 0) * (d + 0 + 1) = (d + 0 + 1) * (zk + 1) := by rw [Nat.mul_comm]
  rw [e1, e2]
  rw [Nat.mul_add, Nat.mul_one] at h3
  have e3 : (d + 0 + 1) * (zk + 1) = (zk + 1) * (d + 0 + 1) := Nat.mul_comm _ _
  omega

theorem odo_dec : ∀ (os os' : List ORec), (∀ x ∈ os, x.Ok) → odoStepR os = some os' →
    ph (os'.map ORec.dgO) < ph (os.map ORec.dgO)
  | [], os', _, h => by simp [odoStepR] at h
  | o :: os, os', hok, h => by
    have ho := hok o (by simp)
    have hd := ho.d
    have hk := ho.k
    unfold odoStepR at h
    cases hn : o.next with
    | inl o' =>
      rw [hn] at h
      simp at h
      subst h
      simp only [ORec.next] at hn
      split at hn
      · injection hn with hn; subst hn
        have := ph_step1 o.d (o.r - o.d - 1) (o.z + o.k - 1) o.m (o.acc.length, o.O) (os.map ORec.dgO) (by omega)
        simp only [List.map_cons, ORec.dgO]
        have e : o.r - (o.d + 1) - 1 = o.r - o.d - 1 - 1 := by omega
        rw [e]
        exact this
      · split at hn
        · injection hn with hn; subst hn
          obtain ⟨m', hm'⟩ : ∃ m', o.m = m' + 1 := ⟨o.m - 1, by omega⟩
          have := ph_step2 o.d (o.z + o.k - 1) m' (o.acc.length, o.O) (os.map ORec.dgO)
          have e0 : o.r - o.d - 1 = 0 := by omega
          have e1 : o.r - 0 - 1 = o.d := by omega
          have e2 : o.z + (o.k + 1) - 1 = o.z + o.k - 1 + 1 := by omega
          have e3 : o.m - 1 = m' := by omega
          simp only [List.map_cons, ORec.dgO, e0, e1, e2, e3, hm'] at this ⊢
          exact this
        · injection hn
    | inr o' =>
      rw [hn] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨os2, hs2, rfl⟩ := h
      have ih := odo_dec os os2 (fun x hx => hok x (by simp [hx])) hs2
      simp only [ORec.next] at hn
      split at hn
      · injection hn
      · split at hn
        · injection hn
        · injection hn with hn; subst hn
          have h0 : o.m = 0 := by omega
          have e0 : o.r - o.d - 1 = 0 := by omega
          have := ph_step3 o.d (o.z + o.k - 1) (o.acc.length, o.O) (os.map ORec.dgO) (os2.map ORec.dgO) ih
          have e1 : o.r - 0 - 1 = o.d := by omega
          have e2 : 0 + 1 - 1 = 0 := by omega
          simp only [List.map_cons, ORec.dgO, e0, e1, h0, e2] at this ⊢
          exact this


theorem dec_m (v : VR) : v.dec.m = v.m := by unfold VR.dec; split <;> rfl
theorem dec_E (v : VR) : v.dec.E = v.E := by unfold VR.dec; split <;> rfl

theorem entryRun (Wf : List Nat) (hW : BitsD Wf) (Kf Cf : List Nat) (hK : BitsD Kf) (hC : BitsD Cf)
    (n m : Nat) (hm : m ≤ n) (o : ORec) (os : List ORec) (hlen : os.length = n)
    (hok : ∀ x ∈ o :: os, x.Ok) (hacc : ∀ x ∈ o :: os, 2 ≤ x.acc.length)
    (p : Nat × Nat) (hp : 1 ≤ p.2)
    (hP2 : GoodW (1 :: (((Kf ++ 1 :: Cf) ++ [1]) ++ NnTail m 0))) :
    let c := (o.vr 3).curG
    let vs := (os.map fun x => x.vr 2).map VR.dec
    let st := hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 ::
          (((Kf ++ 1 :: Cf) ++ [1]) ++ NnTail m 0))) [] c 0 ((o.vr 3).k - 1) ((o.vr 3).w - (o.vr 3).k) vs) []
    (∃ u v os' X R'', Rest u v ∧ ¬ FOk m n c vs ((o.vr 3).k - 1) ((o.vr 3).w - (o.vr 3).k) p 0 (List.replicate n 2) ∧ StepInfo ((c :: vs).map VR.dg) Wf Kf Cf (m + 1 + 0) (p.1 + p.2) v os' ∧ X ++ 3 :: R'' = (v ++ [1, 1]) ++ tapeL os' ∧
      znttLogic.Reach st (hd QNTT.WI0 X (3 :: R''))) ∨
    (∃ (A : List Nat) (n0 : Nat), StepNone ((c :: vs).map VR.dg) ∧ ¬ FOk m n c vs ((o.vr 3).k - 1) ((o.vr 3).w - (o.vr 3).k) p 0 (List.replicate n 2) ∧ znttLogic.Reach st (hd QNTT.BEEP A []) ∧
      ∃ X, znttLogic.zstep (hd QNTT.BEEP A []) = some X ∧
        znttLogic.Reach X (hdR QNTT.PA0 [3] (1 :: (Kf.map (fun x => if x = 1 then 1 else 3) ++ 1 ::
          ((Cf.map (fun x => if x = 1 then 1 else 3) ++ [3]) ++ 1 ::
            (List.replicate (m + 1 + 0) 3 ++ List.replicate (n0 + 1) 0)))))) ∨
    (∃ N : Nat, ∃ T, SuOut ((c :: vs).map VR.dg) Wf (Kf ++ 1 :: Cf) (0 + m + 1) T ∧ FOk m n c vs ((o.vr 3).k - 1) ((o.vr 3).w - (o.vr 3).k) p 0 (List.replicate n 2) ∧
      znttLogic.Reach st (hdR QNTT.SU1 [] T) ∧
      znttLogic.Reach (hdR QNTT.SU1 [] T) (hdR QNTT.PA0 [3] (1 :: (Kf ++ 1 :: (Cf ++ 1 :: (List.replicate (0 + m + 1 + 1) 3 ++
        List.replicate (N + 1) 0)))))) := by
  intro c vs st
  have ho := hok o (by simp)
  have ha := hacc o (by simp)
  have hw : (o.vr 3).Ok := ORec.vr_ok o ho 3 (by simp) ha
  have hvo : ∀ y ∈ os, (y.vr 2).Ok := fun y hy =>
    ORec.vr_ok y (hok y (by simp [hy])) 2 (by simp) (hacc y (by simp [hy]))
  have hm3 : (o.vr 3).m = 0 := by simp [ORec.vr]
  have hcI : CurInv c := curG_inv _ hw (fun _ => hm3)
  have hcw : c.w = (o.vr 3).w := by
    simp only [c, VR.curG]; split <;> simp [VR.cur, dec_w]
  have hcm : c.m = 0 := by
    simp only [c, VR.curG]; split <;> simp [VR.cur, dec_m, hm3]
  have hdp : ∀ v : VR, v.dec.P = v.P := fun v => by unfold VR.dec; split <;> rfl
  have hcP : c.P = 3 := by
    simp only [c, VR.curG]; split <;> simp [VR.cur, hdp, ORec.vr]
  have hvP : ∀ y ∈ os, ((y.vr 2).dec).P = 2 := fun y hy => by simp [hdp, ORec.vr]
  have hw3 : (o.vr 3).w = o.acc.length := by simp [ORec.vr]
  have hk := hw.k1
  have hkw := hw.kw
  have hmem : ∀ x ∈ vs, ∃ y ∈ os, x = (y.vr 2).dec := by
    intro x hx; simp only [vs, List.mem_map] at hx
    obtain ⟨z, ⟨y, hy, rfl⟩, rfl⟩ := hx; exact ⟨y, hy, rfl⟩
  have hvs : ∀ x ∈ vs, x.Ok := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := hmem x hx; exact VR.dec_ok _ (hvo y hy)
  have hom : OutM vs := fun x hx hO => by
    obtain ⟨y, hy, rfl⟩ := hmem x hx; simp [dec_m, ORec.vr]
  have hEFv : ∀ x ∈ vs, EF x := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := hmem x hx
    intro _
    have hl := (hok y (by simp [hy])).Elen
    refine ⟨2, by omega, by simp [dec_E, ORec.vr], ?_⟩
    simp [dec_E, ORec.vr, fld, List.replicate_succ]
  have hvw : ∀ x ∈ vs, 2 ≤ x.w := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := hmem x hx; rw [dec_w]; simpa [ORec.vr] using hacc y (by simp [hy])
  have hvm : ∀ x ∈ vs, x.m = 0 := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := hmem x hx; simp [dec_m, ORec.vr]
  have hfl : c.P :: vs.map VR.P = List.replicate 0 2 ++ 3 :: List.replicate n 2 := by
    rw [hcP]
    have : vs.map VR.P = List.replicate n 2 := by
      apply List.eq_replicate_iff.2
      refine ⟨by simp [vs, hlen], fun x hx => ?_⟩
      simp only [List.mem_map] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      obtain ⟨y, hy, rfl⟩ := hmem z hz; exact hvP y hy
    rw [this]; rfl
  exact assignRunF Wf hW Kf Cf hK hC m 0 n vs c p ((o.vr 3).k - 1) ((o.vr 3).w - (o.vr 3).k) 0
    (List.replicate n 2) hP2 (by omega) (by simp [vs, hlen]) hcI hvs hom hEFv hp (by omega) hvw hcm hvm hfl (by simpa using hm)


theorem entry_dg (o : ORec) (os : List ORec) (ho : o.Ok) (hos : ∀ x ∈ os, x.Ok)
    (_ha : 2 ≤ o.acc.length) :
    ((o.vr 3).curG :: ((os.map fun x => x.vr 2).map VR.dec)).map VR.dg = (o :: os).map ORec.dgO := by
  have h1 : ((o.vr 3).curG).dg = o.dgO := by
    rw [(dg_curG _).1]
    have := o.d; have hd := ho.d; have hk := ho.k
    simp [VR.dg, ORec.vr, ORec.dgO]; omega
  simp only [List.map_cons, h1]
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro x hx
  simp only [Function.comp]
  rw [(dg_dec _).1]
  have hd := (hos x hx).d
  simp [VR.dg, ORec.vr, ORec.dgO]; omega

theorem odo_ok : ∀ (os os' : List ORec), (∀ x ∈ os, x.Ok) → odoStepR os = some os' →
    ∃ o2 os2, os' = o2 :: os2 ∧ os'.length = os.length ∧ (∀ x ∈ o2 :: os2, x.Ok) ∧
      (o2 :: os2).map (fun x => (x.acc.length, x.O)) = os.map (fun x => (x.acc.length, x.O))
  | [], os', _, h => by simp [odoStepR] at h
  | o :: os, os', hok, h => by
    have ho := hok o (by simp)
    unfold odoStepR at h
    cases hn : o.next with
    | inl o' =>
      rw [hn] at h
      simp at h; subst h
      have hok' : o'.Ok ∧ o'.acc = o.acc ∧ o'.O = o.O := by
        simp only [ORec.next] at hn
        split at hn
        · injection hn with hn; subst hn
          exact ⟨{ ho with d := by simp only; have := ho.d; omega }, rfl, rfl⟩
        · split at hn
          · injection hn with hn; subst hn
            exact ⟨{ ho with d := by simp only; have := ho.d; omega, k := by simp only; omega }, rfl, rfl⟩
          · injection hn
      refine ⟨o', os, rfl, by simp, ?_, by simp [hok'.2.1, hok'.2.2]⟩
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hok'.1
      · exact hok x (by simp [hx])
    | inr o' =>
      rw [hn] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨os2, hs2, rfl⟩ := h
      obtain ⟨o3, os3, rfl, hl, hk3, ha3⟩ := odo_ok os os2 (fun x hx => hok x (by simp [hx])) hs2
      have hok' : o'.Ok ∧ o'.acc = o.acc ∧ o'.O = o.O := by
        simp only [ORec.next] at hn
        split at hn
        · injection hn
        · split at hn
          · injection hn
          · injection hn with hn; subst hn
            exact ⟨{ ho with d := by simp only; have := ho.d; omega, k := by simp only; omega }, rfl, rfl⟩
      refine ⟨o', o3 :: os3, rfl, ?_, ?_, ?_⟩
      · simp at hl ⊢; omega
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hok'.1
        · exact hk3 x (by simpa using hx)
      · simp [hok'.2.1, hok'.2.2, ha3]


/-- One odometer step on digit tuples. -/
def DStep (D D2 : List (DG)) : Prop :=
  ∃ (o : ORec) (os : List ORec) (o2 : ORec) (os2 : List ORec), (∀ x ∈ o :: os, x.Ok) ∧ (o :: os).map ORec.dgO = D ∧
    odoStepR (o :: os) = some (o2 :: os2) ∧ (o2 :: os2).map ORec.dgO = D2

inductive DIter : List (DG) → List (DG) → Prop
  | refl (D) : DIter D D
  | step {D D2 D3} : DStep D D2 → DIter D2 D3 → DIter D D3

/-- The pass-start record of a digit tuple. -/
def vrD (g : DG) (x : Nat) : VR :=
  { F := 2, O := g.2.2.2.2.2, P := x, w := g.2.2.2.2.1, k := if x = 3 then 2 else 1,
    E := 3 :: 3 :: List.replicate (g.2.2.2.2.1 - 2) 2, m := 0, n := g.1, s := g.2.1, a := 0, c := g.2.2.1, t := g.2.2.2.1 }

theorem vr_eq_vrD (o : ORec) (h : o.E.length = o.acc.length) (x : Nat) : o.vr x = vrD o.dgO x := by
  simp [ORec.vr, vrD, ORec.dgO, h]; omega

/-- Full success of one assignment, as a function of the digit tuples and the `S` register size. -/
def AOkD (m n : Nat) : List DG → Nat → Prop
  | [], _ => False
  | g :: gs, s => FOk m n (vrD g 3).curG ((gs.map fun x => vrD x 2).map VR.dec) ((vrD g 3).k - 1)
      ((vrD g 3).w - (vrD g 3).k) (0, s) 0 (List.replicate n 2)

theorem AOkD_iff (m n : Nat) (o : ORec) (os : List ORec) (s : Nat) (hok : ∀ x ∈ o :: os, x.Ok) :
    AOkD m n ((o :: os).map ORec.dgO) s ↔
      FOk m n (o.vr 3).curG ((os.map fun x => x.vr 2).map VR.dec) ((o.vr 3).k - 1) ((o.vr 3).w - (o.vr 3).k) (0, s) 0
        (List.replicate n 2) := by
  have h1 : o.vr 3 = vrD o.dgO 3 := vr_eq_vrD o (hok o (by simp)).Elw 3
  have h2 : (os.map fun x => x.vr 2) = (os.map ORec.dgO).map fun x => vrD x 2 := by
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx
    exact vr_eq_vrD x (hok x (by simp [hx])).Elw 2
  simp only [AOkD, List.map_cons]
  rw [h1, h2]

/-- Odometer iteration with all earlier assignments refuted. -/
inductive DIterS (m n s : Nat) : List DG → List DG → Prop
  | refl (D) : DIterS m n s D D
  | step {D D2 D3} : DStep D D2 → ¬ AOkD m n D s → DIterS m n s D2 D3 → DIterS m n s D D3

theorem gw_par (k c n : Nat) (hk : 1 ≤ k) (hc : 1 ≤ c) :
    GoodW (1 :: (((List.replicate k 3 ++ 1 :: List.replicate c 3) ++ [1]) ++ NnTail n 0)) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  have t3 : GoodW (1 :: List.replicate (n + 1) 3) :=
    GoodW.mb (b := 3) (by simp) (GoodW.bits (BitsD.rep n 3 (by simp)))
  have t2 : GoodW (1 :: (List.replicate (c' + 1) 3 ++ 1 :: List.replicate (n + 1) 3)) :=
    GoodW.mb (b := 3) (by simp) (GoodW.app (GoodW.bits (BitsD.rep c' 3 (by simp))) t3)
  have t1 : GoodW (1 :: (List.replicate (k' + 1) 3 ++ 1 :: (List.replicate (c' + 1) 3 ++ 1 :: List.replicate (n + 1) 3))) :=
    GoodW.mb (b := 3) (by simp) (GoodW.app (GoodW.bits (BitsD.rep k' 3 (by simp))) t2)
  simpa [NnTail, List.append_assoc] using t1

theorem map_f_bits {l : List Nat} (h : BitsD l) :
    l.map (fun x => if x = 1 then 1 else 3) = List.replicate l.length 3 := by
  apply List.eq_replicate_iff.2
  refine ⟨by simp, fun y hy => ?_⟩
  simp only [List.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have := h x hx
  simp at this
  rcases this with rfl | rfl <;> simp

theorem par_form (a k c n a' b' : Nat) (S0 : List Nat) (hS0 : BitsD S0) (hN : a' + b' = n + 1 + 0) :
    (List.replicate a 3 ++ 1 :: (S0 ++ 1 :: (((List.replicate k 3 ++ 1 :: List.replicate c 3) ++ [1]) ++ List.replicate a' 3 ++ List.replicate b' 2))).map
      (fun x => if x = 1 then 1 else 3) =
    List.replicate a 3 ++ 1 :: (List.replicate S0.length 3 ++ 1 :: (((List.replicate k 3 ++ 1 :: List.replicate c 3) ++ [1]) ++ NnTail n 0)) := by
  simp only [List.map_append, List.map_cons, List.map_replicate, map_f_bits hS0, NnTail]
  simp [List.append_assoc]
  omega


def loopSt (Wf Kf Cf : List Nat) (m s : Nat) (o : ORec) (os : List ORec) :=
  hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate 0 2 ++ List.replicate s 3 ++ 1 ::
          (((Kf ++ 1 :: Cf) ++ [1]) ++ NnTail m 0))) [] (o.vr 3).curG 0 ((o.vr 3).k - 1)
          ((o.vr 3).w - (o.vr 3).k) ((os.map fun x => x.vr 2).map VR.dec)) []

def LpOut (Wf Kf Cf : List Nat) (m n : Nat) (st : ZC) (D : List (DG)) (s : Nat) : Prop :=
  (∃ (A : List Nat) (n0 : Nat), StepNone D ∧ ¬ AOkD m n D s ∧ znttLogic.Reach st (hd QNTT.BEEP A []) ∧
      ∃ X, znttLogic.zstep (hd QNTT.BEEP A []) = some X ∧
        znttLogic.Reach X (hdR QNTT.PA0 [3] (1 :: (Kf.map (fun x => if x = 1 then 1 else 3) ++ 1 ::
          ((Cf.map (fun x => if x = 1 then 1 else 3) ++ [3]) ++ 1 ::
            (List.replicate (m + 1 + 0) 3 ++ List.replicate (n0 + 1) 0)))))) ∨
    (∃ N : Nat, ∃ T, SuOut D Wf (Kf ++ 1 :: Cf) (0 + m + 1) T ∧ AOkD m n D s ∧
      znttLogic.Reach st (hdR QNTT.SU1 [] T) ∧
      znttLogic.Reach (hdR QNTT.SU1 [] T) (hdR QNTT.PA0 [3] (1 :: (Kf ++ 1 :: (Cf ++ 1 :: (List.replicate (0 + m + 1 + 1) 3 ++
        List.replicate (N + 1) 0))))))

theorem LpOut.pre {Wf Kf Cf m n st st2 D s} (h : znttLogic.Reach st st2) (h2 : LpOut Wf Kf Cf m n st2 D s) :
    LpOut Wf Kf Cf m n st D s := by
  rcases h2 with ⟨A, n0, sn, hn, hb, X, hX, hr⟩ | ⟨N, T, hs, hf, h1, h3⟩
  · exact Or.inl ⟨A, n0, sn, hn, h.trans hb, X, hX, hr⟩
  · exact Or.inr ⟨N, T, hs, hf, h.trans h1, h3⟩

theorem assignLoop (a k c : Nat) (hk : 1 ≤ k) (hc : 1 ≤ c) (n m : Nat) (hm : m ≤ n) :
    ∀ (B s : Nat) (o : ORec) (os : List ORec), ph ((o :: os).map ORec.dgO) = B → 1 ≤ s → os.length = n →
      (∀ x ∈ o :: os, x.Ok) → (∀ x ∈ o :: os, 2 ≤ x.acc.length) →
      ∃ D', DIterS m n s ((o :: os).map ORec.dgO) D' ∧
        LpOut (List.replicate a 3) (List.replicate k 3) (List.replicate c 3) m n
          (loopSt (List.replicate a 3) (List.replicate k 3) (List.replicate c 3) m s o os) D' s := by
  intro B
  induction B using Nat.strongRecOn with
  | _ B ih =>
  intro s o os hB hs hlen hok hacc
  have hP2 := gw_par k c m hk hc
  have hent := entryRun (List.replicate a 3) (BitsD.rep _ _ (by simp)) (List.replicate k 3) (List.replicate c 3)
    (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp)) n m hm o os hlen hok hacc (0, s) hs hP2
  have hD := entry_dg o os (hok o (by simp)) (fun x hx => hok x (by simp [hx])) (hacc o (by simp))
  dsimp only at hent
  rw [hD] at hent
  rcases hent with ⟨u, v, os', X, R'', hrest, hnF, si, e, hr⟩ | hbeep | hsucc
  · obtain ⟨S0, a', b', o1, os1, hS0, hS0ne, hSL, hN, hN1, hok1, hdg1, hst1, hv⟩ := si
    obtain ⟨o2, os2, rfl, hl2, hok2, hacc2⟩ := odo_ok (o1 :: os1) os' hok1 hst1
    have hdec := odo_dec (o1 :: os1) (o2 :: os2) hok1 hst1
    rw [hdg1] at hdec
    have hlen1 : (o1 :: os1).length = (o :: os).length := by
      simpa using congrArg List.length hdg1
    have hlen2 : os2.length = n := by
      simp at hl2 hlen1; omega
    have hvE := par_form a k c m a' b' S0 hS0 hN
    have hvE' := hv.trans hvE
    obtain ⟨s1, hs1⟩ : ∃ s1, S0.length = s1 + 1 := ⟨S0.length - 1, by
      have : S0 ≠ [] := hS0ne
      have := List.length_pos_iff.2 this; omega⟩
    have hSs : s1 + 1 = s := by have := hSL; simp at this; omega
    subst hSs
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    have hvf : v = List.replicate a 3 ++ (1 :: List.replicate (s1 + 1) 3 ++ (1 :: List.replicate (k' + 1) 3 ++
        (1 :: List.replicate (c' + 1) 3 ++ (1 :: List.replicate (m + 1) 3)))) := by
      rw [hvE', hs1]; simp [NnTail, List.append_assoc]
    have hrv : Rest v v := by
      rw [hvf]
      exact Rest.app (rest_rep a) (Rest.app (rest_blk s1) (Rest.app (rest_blk k') (Rest.app (rest_blk c') (rest_blk m))))
    have hnb : NoB ((v ++ [1, 1]) ++ tapeL (o2 :: os2)) := by
      have h1 : NoB v := hrest.goodW.noB
      exact NoB_app_iff.2 ⟨NoB_app_iff.2 ⟨h1, by intro x hx; simp at hx; simp [hx, NB]⟩, tapeL_noB _ hok2⟩
    have hNoB : NoB X := by
      rw [← e] at hnb; exact (NoB_app_iff.1 hnb).1
    have hm0 : (o2 :: os2).map (fun x => (x.acc.length, x.O)) = (o :: os).map (fun x => (x.acc.length, x.O)) := by
      have h1 := congrArg (List.map (fun t : DG => t.2.2.2.2)) hdg1
      simp only [List.map_map, Function.comp_def, ORec.dgO] at h1
      rw [hacc2, ← h1]
    have hm : (o2 :: os2).map (fun x => x.acc.length) = (o :: os).map (fun x => x.acc.length) := by
      have := congrArg (List.map Prod.fst) hm0
      simpa [List.map_map, Function.comp_def] using this
    have hacc2' : ∀ x ∈ o2 :: os2, 2 ≤ x.acc.length := by
      intro x hx
      have h1 : x.acc.length ∈ (o2 :: os2).map (fun x => x.acc.length) := List.mem_map_of_mem hx
      rw [hm] at h1
      obtain ⟨y, hy, hyx⟩ := List.mem_map.1 h1
      rw [← hyx]; exact hacc y hy
    have hnext := nextEntry X R'' v hNoB hrv o2 os2 hok2 hacc2' e
    rw [hvE', hs1] at hnext
    obtain ⟨D', hit, hout⟩ := ih _ (by omega) (s1 + 1) o2 os2 rfl (by omega) hlen2 hok2 hacc2'
    refine ⟨D', DIterS.step ⟨o1, os1, o2, os2, hok1, hdg1, hst1, rfl⟩ ?_ hit, ?_⟩
    · rw [AOkD_iff m n o os (s1 + 1) hok]; exact hnF
    · exact LpOut.pre (hr.trans hnext) hout
  · obtain ⟨A, n0, sn, hnF, hb, X, hX, hXr⟩ := hbeep
    refine ⟨_, DIterS.refl _, Or.inl ⟨A, n0, sn, ?_, hb, X, hX, hXr⟩⟩
    rw [AOkD_iff m n o os s hok]; exact hnF
  · obtain ⟨N, T, hs, hf, h1, h2⟩ := hsucc
    refine ⟨_, DIterS.refl _, Or.inr ⟨N, T, hs, ?_, h1, h2⟩⟩
    rw [AOkD_iff m n o os s hok]; exact hf


theorem incK_val (w k : Nat) (hk : 1 ≤ k) (hkw : k ≤ w) : incK w k - 1 = (k - 1 + 1) % w := by
  unfold incK
  split
  · subst_vars; have : k - 1 + 1 = k := by omega
    rw [this, Nat.mod_self]
  · have : k - 1 + 1 = k := by omega
    rw [this, Nat.mod_eq_of_lt (by omega)]; omega

theorem incKn_val (w : Nat) : ∀ (n k : Nat), 1 ≤ k → k ≤ w → 1 ≤ incKn w n k ∧ incKn w n k ≤ w ∧
    incKn w n k - 1 = (k - 1 + n) % w
  | 0, k, hk, hkw => by
    refine ⟨hk, hkw, ?_⟩
    simp [incKn]; rw [Nat.mod_eq_of_lt (by omega)]
  | n + 1, k, hk, hkw => by
    have h1 := incK_bounds w k hk hkw
    obtain ⟨a, b, c⟩ := incKn_val w n (incK w k) h1.1 h1.2
    refine ⟨a, b, ?_⟩
    simp only [incKn]
    rw [c, incK_val w k hk hkw, Nat.mod_add_mod]
    congr 1; omega

/-- Every record carries the invariants `Ok` and `m = 0`. -/
def VI (v : VR) : Prop := v.Ok ∧ v.m = 0

theorem vis_fields (v : VR) (h : VI v) :
    VI v.vis ∧ v.vis.w = v.w ∧ v.vis.c = v.c ∧ v.vis.n = v.n ∧ v.vis.a = v.a ∧ v.vis.t = v.t ∧ v.vis.O = v.O ∧
    v.vis.E = v.E ∧ v.vis.P = v.P ∧
    v.vis.k - 1 = (v.k - 1 + (if v.c = 1 then v.n else 0)) % v.w := by
  obtain ⟨ho, hm⟩ := h
  by_cases hc : v.c = 1
  · have hb := incKn_val v.w v.n v.k ho.k1 ho.kw
    have e : v.vis = { v with k := incKn v.w v.n v.k, m := 0, n := v.n } := by
      unfold VR.vis; rw [if_pos hc, hm, Nat.zero_add]
    rw [e, if_pos hc]
    exact ⟨⟨{ F := ho.F, O := ho.O, P := ho.P, k1 := hb.1, kw := hb.2.1, E := ho.E, Elen := ho.Elen, Elw := ho.Elw }, rfl⟩,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hb.2.2⟩
  · have e : v.vis = v := by unfold VR.vis; rw [if_neg hc]
    rw [e, if_neg hc]
    refine ⟨⟨ho, hm⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    rw [Nat.add_zero, Nat.mod_eq_of_lt (by have := ho.kw; have := ho.k1; omega)]

theorem inc_fields (v : VR) (h : VI v) :
    VI v.inc ∧ v.inc.w = v.w ∧ v.inc.c = v.c ∧ v.inc.n = v.n ∧ v.inc.a = v.a ∧ v.inc.t = v.t ∧ v.inc.O = v.O ∧
    v.inc.E = v.E ∧ v.inc.P = v.P ∧ v.inc.k - 1 = (v.k - 1 + 1) % v.w := by
  obtain ⟨ho, hm⟩ := h
  exact ⟨⟨ho.inc, hm⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, incK_val v.w v.k ho.k1 ho.kw⟩

def visN : Nat → VR → VR
  | 0, v => v
  | r + 1, v => visN r v.vis

/-- Value `k - 1` of a record after `r` visits. -/
theorem visIter (r : Nat) : ∀ v : VR, VI v →
    VI (visN r v) ∧ (visN r v).w = v.w ∧ (visN r v).c = v.c ∧ (visN r v).n = v.n ∧
    (visN r v).a = v.a ∧ (visN r v).t = v.t ∧ (visN r v).O = v.O ∧ (visN r v).E = v.E ∧
    (visN r v).P = v.P ∧
    (visN r v).k - 1 = (v.k - 1 + r * (if v.c = 1 then v.n else 0)) % v.w := by
  induction r with
  | zero =>
    intro v h
    refine ⟨h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    show v.k - 1 = (v.k - 1 + 0 * (if v.c = 1 then v.n else 0)) % v.w
    rw [Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt (by have := h.1.kw; have := h.1.k1; omega)]
  | succ r ih =>
    intro v h
    simp only [visN]
    obtain ⟨h1, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := vis_fields v h
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ := ih v.vis h1
    refine ⟨g1, by rw [g2, e1], by rw [g3, e2], by rw [g4, e3], by rw [g5, e4], by rw [g6, e5],
      by rw [g7, e6], by rw [g8, e7], by rw [g9, e8], ?_⟩
    rw [g10, e9, e2, e1, e3]
    rw [Nat.mod_add_mod, Nat.succ_mul]
    congr 1
    by_cases hc : v.c = 1
    · simp only [if_pos hc]
      generalize r * v.n = X
      omega
    · simp only [if_neg hc]
      simp

def incVisN : Nat → VR → VR
  | 0, v => v
  | r + 1, v => incVisN r v.inc.vis

theorem incVisN_val (r : Nat) : ∀ v : VR, VI v →
    VI (incVisN r v) ∧ (incVisN r v).w = v.w ∧ (incVisN r v).c = v.c ∧ (incVisN r v).n = v.n ∧
    (incVisN r v).a = v.a ∧ (incVisN r v).t = v.t ∧ (incVisN r v).O = v.O ∧ (incVisN r v).E = v.E ∧
    (incVisN r v).P = v.P ∧
    (incVisN r v).k - 1 = (v.k - 1 + r * (1 + (if v.c = 1 then v.n else 0))) % v.w := by
  induction r with
  | zero =>
    intro v h
    refine ⟨h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    show v.k - 1 = (v.k - 1 + 0 * (1 + (if v.c = 1 then v.n else 0))) % v.w
    rw [Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt (by have := h.1.kw; have := h.1.k1; omega)]
  | succ r ih =>
    intro v h
    simp only [incVisN]
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := inc_fields v h
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := vis_fields v.inc a1
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ := ih v.inc.vis b1
    refine ⟨g1, by rw [g2, b2, a2], by rw [g3, b3, a3], by rw [g4, b4, a4], by rw [g5, b5, a5],
      by rw [g6, b6, a6], by rw [g7, b7, a7], by rw [g8, b8, a8], by rw [g9, b9, a9], ?_⟩
    rw [g10, b10, a10, b3, b2, a3, a2, b4, a4, Nat.mod_add_mod, Nat.add_assoc, Nat.mod_add_mod]
    congr 1
    rw [Nat.succ_mul]
    generalize r * (1 + if v.c = 1 then v.n else 0) = X
    omega

theorem stepN_cons (r : Nat) : ∀ (w : VR) (ws : List VR), stepN r (w :: ws) = incVisN r w :: ws.map (visN r) := by
  induction r with
  | zero => intro w ws; simp [stepN, incVisN, visN]
  | succ r ih =>
    intro w ws
    simp only [stepN, stepList]
    rw [ih]
    simp [incVisN, visN, List.map_map, Function.comp_def]


theorem valsAux_prefix (t p : Nat) : ∀ (recs : List Rec) (j : Nat) (vs : List Nat),
    vs <+: valsAux t p j recs vs ∧ (valsAux t p j recs vs).length = vs.length + recs.length
  | [], j, vs => by simp [valsAux]
  | (u, b) :: rs, j, vs => by
    obtain ⟨h1, h2⟩ := valsAux_prefix t p rs (j + 1) (vs ++ [((if j = t then 1 else 0) + vs.getLastD 0 + ptrVal u j b vs) % p])
    simp only [valsAux]
    refine ⟨(List.prefix_append _ _).trans h1, ?_⟩
    rw [h2]; simp; omega

theorem getD_prefix {l1 l2 : List Nat} (h : l1 <+: l2) {i : Nat} (hi : i < l1.length) : l2.getD i 0 = l1.getD i 0 := by
  obtain ⟨k, rfl⟩ := h
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem valsAux_get (t p : Nat) : ∀ (recs : List Rec) (j : Nat) (vs : List Nat), vs.length = j →
    ∀ i, j ≤ i → i < j + recs.length →
    (valsAux t p j recs vs).getD i 0 =
      ((if i = t then 1 else 0) + (if i = 0 then 0 else (valsAux t p j recs vs).getD (i - 1) 0) +
        ptrVal (recs.getD (i - j) (none, 0)).1 i (recs.getD (i - j) (none, 0)).2 (valsAux t p j recs vs)) % p
  | [], j, vs, hl, i, h1, h2 => by simp at h2; omega
  | (u, b) :: rs, j, vs, hl, i, h1, h2 => by
    obtain ⟨v, hv⟩ : ∃ v, v = ((if j = t then 1 else 0) + vs.getLastD 0 + ptrVal u j b vs) % p := ⟨_, rfl⟩
    have hlen : (vs ++ [v]).length = j + 1 := by simp [hl]
    have pre := (valsAux_prefix t p rs (j + 1) (vs ++ [v])).1
    simp only [valsAux]
    rw [← hv]
    by_cases hij : i = j
    · subst hij
      have e1 : (valsAux t p (i + 1) rs (vs ++ [v])).getD i 0 = v := by
        rw [getD_prefix pre (by omega)]
        simp [hl]
      rw [e1]
      simp only [Nat.sub_self, List.getD_cons_zero]
      have e2 : vs.getLastD 0 = (if i = 0 then 0 else (valsAux t p (i + 1) rs (vs ++ [v])).getD (i - 1) 0) := by
        by_cases h0 : i = 0
        · subst h0; have : vs = [] := List.length_eq_zero_iff.1 hl
          subst this; simp
        · rw [if_neg h0, getD_prefix pre (by simp [hl]; omega)]
          have : vs ≠ [] := by intro h; subst h; simp at hl; omega
          rw [List.getLastD_eq_getLast?, List.getD_eq_getElem?_getD, List.getLast?_eq_getElem?]
          rw [List.getElem?_append_left (by omega)]
          simp [hl]
      have e3 : ptrVal u i b vs = ptrVal u i b (valsAux t p (i + 1) rs (vs ++ [v])) := by
        unfold ptrVal
        cases u with
        | none => rfl
        | some u =>
          simp only
          split
          · rename_i hu
            rw [getD_prefix pre (by simp [hl]; omega)]
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
          · rfl
      conv => lhs; rw [hv, e2, e3]
    · have := valsAux_get t p rs (j + 1) (vs ++ [v]) hlen i (by omega) (by simp at h2 ⊢; omega)
      rw [this]
      have : i - j = (i - (j + 1)) + 1 := by omega
      rw [this]
      simp


def ptrOf (π : Nat) : Option Nat := if 2 ≤ π then some (π - 2) else none

/-- Per-record column invariant at column `j`. -/
def RecI (p T j π d : Nat) (vals : List Nat) (chain : Nat) (x : VR) : Prop :=
  VI x ∧ x.w = p ∧ x.n = d ∧ x.a + x.c = π ∧ x.a = min π (j + 1) ∧
    x.k - 1 = (T + chain + ptrVal (ptrOf π) j d vals) % p

theorem dec_fields' (v : VR) : v.dec.n = v.n ∧ v.dec.m = v.m ∧ v.dec.k = v.k ∧ v.dec.w = v.w ∧
    v.dec.a + v.dec.c = v.a + v.c ∧ (v.c = 0 → v.dec.a = v.a) ∧ (v.c ≠ 0 → v.dec.a = v.a + 1 ∧ v.dec.c = v.c - 1) := by
  unfold VR.dec
  by_cases h : v.c = 0
  · simp [h]
  · simp [h]; omega

theorem curG_f (v : VR) (h : VI v) : VI v.curG ∧ v.curG.n = v.dec.n ∧ v.curG.k = v.dec.k ∧ v.curG.w = v.dec.w ∧
    v.curG.a = v.dec.a ∧ v.curG.c = v.dec.c := by
  have hI : VI v.dec := ⟨v.dec_ok h.1, by rw [(dec_fields' v).2.1]; exact h.2⟩
  have hm : v.O = 3 → v.m = 0 := fun _ => h.2
  have hc := (curG_inv v h.1 hm).1
  have hmm := (dg_curG v).2
  refine ⟨⟨hc, by rw [hmm]; exact h.2⟩, ?_⟩
  unfold VR.curG
  split <;> simp [VR.cur]

theorem ptrVal_succ (π d j : Nat) (vals : List Nat) :
    ptrVal (ptrOf π) (j + 1) d vals = ptrVal (ptrOf π) j d vals + (if π = j + 2 then d * vals.getD j 0 else 0) := by
  unfold ptrVal ptrOf
  by_cases h : 2 ≤ π
  · simp only [h, if_true]
    by_cases h1 : π - 2 < j
    · have : π ≠ j + 2 := by omega
      simp [h1, this]; omega
    · by_cases h2 : π = j + 2
      · have e : π - 2 = j := by omega
        simp [e, h2]
      · have : ¬ (π - 2 < j + 1) := by omega
        simp [h1, this, h2]
  · simp only [h, if_false]
    have : π ≠ j + 2 := by omega
    simp [this]

theorem c1_iff (π j : Nat) (x : VR) (hac : x.a + x.c = π) (ha : x.a = min π (j + 1)) :
    (x.c = 1 ↔ π = j + 2) := by omega

theorem dec_a_min (π j : Nat) (y : VR) (hac : y.a + y.c = π) (ha : y.a = min π (j + 1)) :
    y.dec.a = min π (j + 1 + 1) := by
  have df := dec_fields' y
  by_cases h : y.c = 0
  · rw [df.2.2.2.2.2.1 h]; omega
  · rw [(df.2.2.2.2.2.2 h).1]; omega

theorem recI_tail (p T j π d : Nat) (vals : List Nat) (x : VR) (r : Nat) (hp : 0 < p)
    (h : RecI p T j π d vals 0 x) (hr : r = vals.getD j 0) :
    RecI p T (j + 1) π d vals 0 (VR.dec (visN r x)) := by
  obtain ⟨hI, hw, hn, hac, ha, hk⟩ := h
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := visIter r x hI
  have df := dec_fields' (visN r x)
  have hI' : VI (VR.dec (visN r x)) := ⟨(visN r x).dec_ok v1.1, by rw [df.2.1]; exact v1.2⟩
  have hac' : (visN r x).a + (visN r x).c = π := by rw [v3, v5]; exact hac
  have ha' : (visN r x).a = min π (j + 1) := by rw [v5]; exact ha
  refine ⟨hI', by rw [df.2.2.2.1, v2, hw], by rw [df.1, v4, hn], by rw [df.2.2.2.2.1]; exact hac',
    dec_a_min π j _ hac' ha', ?_⟩
  rw [df.2.2.1]
  rw [v10, hw, hk, Nat.mod_add_mod, ptrVal_succ]
  have := c1_iff π j x hac ha
  by_cases hc : x.c = 1
  · have h2 : π = j + 2 := this.1 hc
    simp only [if_pos hc, if_pos h2, hn]
    have e : r * d = d * vals.getD j 0 := by rw [hr, Nat.mul_comm]
    rw [e, Nat.add_assoc]
  · have h2 : ¬ π = j + 2 := fun e => hc (this.2 e)
    simp only [if_neg hc, if_neg h2, Nat.mul_zero, Nat.add_zero]

theorem recI_head (p T j π d : Nat) (vals : List Nat) (x : VR) (r : Nat) (hp : 0 < p)
    (h : RecI p T j π d vals 0 x) (hr : r = vals.getD j 0) :
    RecI p T (j + 1) π d vals r (VR.curG (incVisN r x)) := by
  obtain ⟨hI, hw, hn, hac, ha, hk⟩ := h
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := incVisN_val r x hI
  have df := dec_fields' (incVisN r x)
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := curG_f _ v1
  have hac' : (incVisN r x).a + (incVisN r x).c = π := by rw [v3, v5]; exact hac
  have ha' : (incVisN r x).a = min π (j + 1) := by rw [v5]; exact ha
  refine ⟨g1, by rw [g4, df.2.2.2.1, v2, hw], by rw [g2, df.1, v4, hn], ?_, ?_, ?_⟩
  · rw [g5, g6, df.2.2.2.2.1]; exact hac'
  · rw [g5]; exact dec_a_min π j _ hac' ha'
  · rw [g3, df.2.2.1, v10, hw, hk, Nat.mod_add_mod, ptrVal_succ]
    have := c1_iff π j x hac ha
    by_cases hc : x.c = 1
    · have h2 : π = j + 2 := this.1 hc
      simp only [if_pos hc, if_pos h2, hn]
      have e : r * (1 + d) = r + d * r := by rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm r d]
      rw [e, ← hr]
      congr 1; omega
    · have h2 : ¬ π = j + 2 := fun e => hc (this.2 e)
      simp only [if_neg hc, if_neg h2, Nat.add_zero, Nat.mul_zero]
      congr 1; omega

def ColInv (p t j : Nat) (πs ds vals : List Nat) (xs : List VR) : Prop :=
  ∀ idx x, xs[idx]? = some x →
    RecI p (if j + idx = t then 1 else 0) j (πs.getD (j + idx) 0) (ds.getD (j + idx) 0) vals
      (if idx = 0 then (if j = 0 then 0 else vals.getD (j - 1) 0) else 0) x

def ValsOk (p t N : Nat) (πs ds vals : List Nat) : Prop :=
  ∀ i, i < N → vals.getD i 0 =
    ((if i = t then 1 else 0) + (if i = 0 then 0 else vals.getD (i - 1) 0) +
      ptrVal (ptrOf (πs.getD i 0)) i (ds.getD i 0) vals) % p

theorem cursor_val (p t N : Nat) (πs ds vals : List Nat) (hV : ValsOk p t N πs ds vals) (j : Nat) (c : VR)
    (vs : List VR) (hj : j < N) (hI : ColInv p t j πs ds vals (c :: vs)) : c.k - 1 = vals.getD j 0 := by
  obtain ⟨_, _, _, _, _, hk⟩ := hI 0 c (by simp)
  rw [hk, hV j hj]
  simp

theorem loopVals (p t N : Nat) (πs ds vals : List Nat) (hp : 0 < p) (hV : ValsOk p t N πs ds vals) :
    ∀ (n j : Nat) (c : VR) (vs : List VR) (r s : Nat) (pp : Nat × Nat), vs.length = n → j + n + 1 = N →
      ColInv p t j πs ds vals (c :: vs) → r = c.k - 1 →
      (loopRun n c vs r s pp).cs.map (fun x => x.1.k - 1) = (List.range n).map (fun i => vals.getD (j + i) 0) ∧
      (loopRun n c vs r s pp).c'.k - 1 = vals.getD (j + n) 0 := by
  intro n
  induction n with
  | zero =>
    intro j c vs r s pp hl hN hI hr
    have hvs : vs = [] := List.length_eq_zero_iff.1 hl
    subst hvs
    simp only [loopRun, List.range_zero, List.map_nil, true_and]
    exact cursor_val p t N πs ds vals hV j c [] (by omega) hI
  | succ n ih =>
    intro j c vs r s pp hl hN hI hr
    obtain ⟨v0, vs', rfl⟩ : ∃ v0 vs', vs = v0 :: vs' := by
      cases vs with
      | nil => simp at hl
      | cons a b => exact ⟨a, b, rfl⟩
    have hrj : r = vals.getD j 0 := by
      rw [hr]; exact cursor_val p t N πs ds vals hV j c _ (by omega) hI
    have h0 := hI 1 v0 (by simp)
    simp only [show ¬ ((1:Nat) = 0) from by decide, if_false] at h0
    have hhead := recI_head p _ j _ _ vals v0 r hp h0 hrj
    have hI' : ColInv p t (j + 1) πs ds vals
        (VR.curG (incVisN r v0) :: (vs'.map (visN r)).map VR.dec) := by
      intro idx x hx
      cases idx with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        have e : (if (0:Nat) = 0 then (if j + 1 = 0 then 0 else vals.getD (j + 1 - 1) 0) else 0) = r := by
          simp [hrj]
        rw [e]; exact hhead
      | succ idx =>
        simp only [List.getElem?_cons_succ, List.getElem?_map, Option.map_eq_some_iff] at hx
        obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := hx
        have hz' : (c :: v0 :: vs')[idx + 2]? = some z := by simpa using hz
        have h1 := hI (idx + 2) z hz'
        have e : j + 1 + (idx + 1) = j + (idx + 2) := by omega
        rw [e]
        simp only [show ¬ (idx + 2 = 0) from by omega, if_false] at h1
        simp only [show ¬ (idx + 1 = 0) from by omega, if_false]
        exact recI_tail p _ j _ _ vals z r hp h1 hrj
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := curG_f (incVisN r v0) (incVisN_val r v0 h0.1).1
    have df := dec_fields' (incVisN r v0)
    have hr' : (incVisN r v0).k - 1 = (VR.curG (incVisN r v0)).k - 1 := by rw [g3, df.2.2.1]
    have hl' : ((vs'.map (visN r)).map VR.dec).length = n := by simp at hl ⊢; omega
    have IH := ih (j + 1) (VR.curG (incVisN r v0)) _ ((incVisN r v0).k - 1) ((incVisN r v0).w - (incVisN r v0).k)
      (outP c r pp) hl' (by omega) hI' hr'
    have hk : (outRec c r).k = c.k := by unfold outRec; split <;> rfl
    simp only [loopRun, stepN_cons]
    refine ⟨?_, ?_⟩
    · rw [List.range_succ_eq_map, List.map_cons, List.map_cons]
      refine List.cons_eq_cons.2 ⟨?_, ?_⟩
      · simp only [hk, Nat.add_zero]; rw [← hr]; exact hrj.symm ▸ rfl
      · rw [IH.1, List.map_map]
        apply List.map_congr_left
        intro i _
        simp only [Function.comp]
        congr 1; omega
    · have := IH.2
      rw [this]; congr 1; omega


theorem eAdv_val (w : Nat) : ∀ (n e : Nat), 1 ≤ e → e ≤ w → 1 ≤ eAdv w n e ∧ eAdv w n e ≤ w ∧
    eAdv w n e - 1 = (e - 1 + n) % w
  | 0, e, h1, h2 => by
    refine ⟨h1, h2, ?_⟩
    simp [eAdv]; rw [Nat.mod_eq_of_lt (by omega)]
  | n + 1, e, h1, h2 => by
    have hb := incK_bounds w e h1 h2
    obtain ⟨a, b, c⟩ := eAdv_val w n (incK w e) hb.1 hb.2
    refine ⟨a, b, ?_⟩
    simp only [eAdv]
    rw [c, incK_val w e h1 h2, Nat.mod_add_mod]
    congr 1; omega

theorem sAdv_val : ∀ (n : Nat) (p : Nat × Nat), 1 ≤ p.2 →
    (sAdv n p).1 + (sAdv n p).2 = p.1 + p.2 ∧ 1 ≤ (sAdv n p).2 ∧
    (sAdv n p).1 = (p.1 + n) % (p.1 + p.2)
  | 0, p, h => by
    refine ⟨rfl, h, ?_⟩
    simp [sAdv]; rw [Nat.mod_eq_of_lt (by omega)]
  | n + 1, p, h => by
    have hn : 1 ≤ (sNext p).2 ∧ (sNext p).1 + (sNext p).2 = p.1 + p.2 := by
      unfold sNext; split <;> simp <;> omega
    obtain ⟨a, b, c⟩ := sAdv_val n (sNext p) hn.1
    simp only [sAdv]
    refine ⟨by rw [a]; exact hn.2, b, ?_⟩
    rw [c, hn.2]
    have : (sNext p).1 = (p.1 + 1) % (p.1 + p.2) := by
      unfold sNext
      split
      · rename_i h2
        have : p.1 + 1 = p.1 + p.2 := by omega
        rw [this, Nat.mod_self]
      · rw [Nat.mod_eq_of_lt (by omega)]
    rw [this, Nat.mod_add_mod]
    congr 1; omega

theorem count3_fld' (len e : Nat) (h : e ≤ len) : (fld len e).count 3 = e := by
  simp [fld, List.count_replicate]

/-- The `E` register of a finished output cursor: value `z * acc` (it was reset to value 0 by `curG`). -/
theorem outRec_E (c : VR) (r : Nat) (hO : c.O = 3) (hE : c.E = fld c.E.length 1) (hl : 1 ≤ c.E.length) :
    ∃ e, 1 ≤ e ∧ e ≤ c.E.length ∧ (outRec c r).E = fld c.E.length e ∧ e - 1 = (r * c.n) % c.E.length := by
  unfold outRec
  rw [if_neg (by omega)]
  have hc : c.E.count 3 = 1 := by rw [hE]; exact count3_fld' _ _ hl |>.trans rfl
  have := eAdv_val c.E.length (r * c.n) 1 (by omega) hl
  refine ⟨eAdv c.E.length (r * c.n) (c.E.count 3), ?_⟩
  rw [hc]
  refine ⟨this.1, this.2.1, rfl, ?_⟩
  rw [this.2.2]; simp


/-- A record at the start of pass `t` (before the first decrement). -/
def StartRec (p T π d : Nat) (y : VR) : Prop :=
  VI y ∧ y.w = p ∧ y.n = d ∧ y.a = 0 ∧ y.a + y.c = π ∧ y.k = T + 1

theorem recI_start_dec (p T π d : Nat) (vals : List Nat) (y : VR) (hp : 2 ≤ p) (hT : T ≤ 1)
    (h : StartRec p T π d y) : RecI p T 0 π d vals 0 y.dec := by
  obtain ⟨hI, hw, hn, ha, hac, hk⟩ := h
  have df := dec_fields' y
  have hdI : VI y.dec := ⟨y.dec_ok hI.1, by rw [df.2.1]; exact hI.2⟩
  refine ⟨hdI, by rw [df.2.2.2.1, hw], by rw [df.1, hn], by rw [df.2.2.2.2.1]; exact hac, ?_, ?_⟩
  · by_cases hc : y.c = 0
    · rw [df.2.2.2.2.2.1 hc]; omega
    · rw [(df.2.2.2.2.2.2 hc).1]; omega
  · rw [df.2.2.1, hk]
    have : ptrVal (ptrOf π) 0 d vals = 0 := by
      unfold ptrVal; cases ptrOf π <;> simp
    rw [this, Nat.add_zero, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]; rfl

theorem recI_start_cur (p T π d : Nat) (vals : List Nat) (y : VR) (hp : 2 ≤ p) (hT : T ≤ 1)
    (h : StartRec p T π d y) : RecI p T 0 π d vals 0 y.curG := by
  have hd := recI_start_dec p T π d vals y hp hT h
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := curG_f y h.1
  obtain ⟨_, hw, hn, hac, ha, hk⟩ := hd
  refine ⟨g1, by rw [g4]; exact hw, by rw [g2]; exact hn, by rw [g5, g6]; exact hac, by rw [g5]; exact ha, ?_⟩
  rw [g3]; exact hk

theorem startColInv (p t : Nat) (πs ds vals : List Nat) (hp : 2 ≤ p) (y0 : VR) (ys : List VR)
    (hy : ∀ idx y, (y0 :: ys)[idx]? = some y →
      StartRec p (if idx = t then 1 else 0) (πs.getD idx 0) (ds.getD idx 0) y) :
    ColInv p t 0 πs ds vals (y0.curG :: ys.map VR.dec) := by
  intro idx x hx
  cases idx with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
    subst hx
    have := recI_start_cur p _ (πs.getD 0 0) (ds.getD 0 0) vals y0 hp (by split <;> omega) (hy 0 y0 (by simp))
    simpa using this
  | succ idx =>
    simp only [List.getElem?_cons_succ, List.getElem?_map, Option.map_eq_some_iff] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    have := recI_start_dec p _ (πs.getD (idx + 1) 0) (ds.getD (idx + 1) 0) vals z hp (by split <;> omega)
      (hy (idx + 1) z (by simpa using hz))
    simpa using this


theorem nextPass_start (p T j π d : Nat) (vals : List Nat) (ch : Nat) (c : VR) (x : Nat) (hp : 2 ≤ p)
    (hx : x ∈ [2, 3]) (h : RecI p T j π d vals ch c) :
    StartRec p (if x = 3 then 1 else 0) π d (c.nextPass x) := by
  obtain ⟨⟨hok, hm⟩, hw, hn, hac, ha, hk⟩ := h
  have hxx : x = 2 ∨ x = 3 := by simpa using hx
  have hOk : (c.nextPass x).Ok := by
    refine { F := ?_, O := ?_, P := ?_, k1 := ?_, kw := ?_, E := ?_, Elen := ?_, Elw := ?_ }
    · simp [VR.nextPass]
    · exact hok.O
    · simpa [VR.nextPass] using hx
    · simp [VR.nextPass]; split <;> omega
    · simp [VR.nextPass, hw]; split <;> omega
    · exact hok.E
    · exact hok.Elen
    · exact hok.Elw
  have hI : VI (c.nextPass x) := ⟨hOk, hm⟩
  refine ⟨hI, hw, hn, rfl, ?_, ?_⟩
  · simp [VR.nextPass]; omega
  · simp [VR.nextPass]; rcases hxx with rfl | rfl <;> simp


/-- One pass from its start records: the finished records carry the node values. -/
theorem passVals (p t : Nat) (πs ds vals : List Nat) (hp : 2 ≤ p) (y0 : VR) (ys : List VR)
    (hy : ∀ idx y, (y0 :: ys)[idx]? = some y →
      StartRec p (if idx = t then 1 else 0) (πs.getD idx 0) (ds.getD idx 0) y)
    (hV : ValsOk p t (ys.length + 1) πs ds vals) (s : Nat) (pp : Nat × Nat) :
    (loopRun ys.length y0.curG (ys.map VR.dec) (y0.curG.k - 1) s pp).cs.map (fun x => x.1.k - 1) =
      (List.range ys.length).map (fun i => vals.getD i 0) ∧
    (loopRun ys.length y0.curG (ys.map VR.dec) (y0.curG.k - 1) s pp).c'.k - 1 = vals.getD ys.length 0 := by
  have hI := startColInv p t πs ds vals hp y0 ys hy
  have := loopVals p t (ys.length + 1) πs ds vals (by omega) hV ys.length 0 y0.curG (ys.map VR.dec)
    (y0.curG.k - 1) s pp (by simp) (by omega) hI rfl
  simpa using this


def decRecs : List Nat → List Nat → List Rec
  | π :: πs, d :: ds => (ptrOf π, d) :: decRecs πs ds
  | _, _ => []

def DigOk (p : Nat) : Nat → List Nat → List Nat → Prop
  | _, [], [] => True
  | j, π :: πs, d :: ds => π ≤ j + 1 ∧ d < p ∧ DigOk p (j + 1) πs ds
  | _, _, _ => False

theorem mem_recChoices (j p : Nat) (r : Rec) :
    r ∈ recChoices j p ↔ ∃ π d, π ≤ j + 1 ∧ d < p ∧ r = (ptrOf π, d) := by
  unfold recChoices
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap]
  constructor
  · rintro (⟨b, hb, rfl⟩ | ⟨u, hu, b, hb, rfl⟩)
    · exact ⟨0, b, by omega, hb, by simp [ptrOf]⟩
    · exact ⟨u + 2, b, by omega, hb, by simp [ptrOf]⟩
  · rintro ⟨π, d, h1, h2, rfl⟩
    by_cases h : 2 ≤ π
    · right; exact ⟨π - 2, by omega, d, h2, by simp [ptrOf, h]⟩
    · left; exact ⟨d, h2, by simp [ptrOf, h]⟩

theorem mem_allRecs (p : Nat) : ∀ (N j : Nat) (recs : List Rec), recs ∈ allRecs p N j ↔
    ∃ πs ds, DigOk p j πs ds ∧ πs.length = N ∧ decRecs πs ds = recs
  | 0, j, recs => by
    simp only [allRecs, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨[], [], trivial, rfl, rfl⟩
    · rintro ⟨πs, ds, h, hl, rfl⟩
      have : πs = [] := List.length_eq_zero_iff.1 hl
      subst this
      cases ds <;> simp [DigOk, decRecs] at h ⊢
  | N + 1, j, recs => by
    simp only [allRecs, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨r, hr, rs, hrs, rfl⟩
      obtain ⟨π, d, h1, h2, rfl⟩ := (mem_recChoices j p r).1 hr
      obtain ⟨πs, ds, hd, hl, rfl⟩ := (mem_allRecs p N (j + 1) rs).1 hrs
      exact ⟨π :: πs, d :: ds, ⟨h1, h2, hd⟩, by simp [hl], rfl⟩
    · rintro ⟨πs, ds, hd, hl, rfl⟩
      cases πs with
      | nil => simp at hl
      | cons π πs =>
        cases ds with
        | nil => simp [DigOk] at hd
        | cons d ds =>
          obtain ⟨h1, h2, hd'⟩ := hd
          refine ⟨(ptrOf π, d), (mem_recChoices j p _).2 ⟨π, d, h1, h2, rfl⟩, decRecs πs ds,
            (mem_allRecs p N (j + 1) _).2 ⟨πs, ds, hd', by simpa using hl, rfl⟩, rfl⟩

theorem hasCircuit_iff (pr : Nat → Nat) (c n : Nat) : hasCircuit pr c n = true ↔
    ∃ πs ds, DigOk (pr n) 0 πs ds ∧ πs.length = c * n ∧ evalC n (pr n) (decRecs πs ds) = true := by
  unfold hasCircuit
  rw [List.any_eq_true]
  constructor
  · rintro ⟨recs, hm, he⟩
    obtain ⟨πs, ds, h1, h2, rfl⟩ := (mem_allRecs _ _ _ recs).1 hm
    exact ⟨πs, ds, h1, h2, he⟩
  · rintro ⟨πs, ds, h1, h2, he⟩
    exact ⟨_, (mem_allRecs _ _ _ _).2 ⟨πs, ds, h1, h2, rfl⟩, he⟩


inductive Rt {α : Type} (R : α → α → Prop) : α → α → Prop
  | refl (a : α) : Rt R a a
  | tail {a b c : α} : Rt R a b → R b c → Rt R a c

theorem Rt.trans {α : Type} {R : α → α → Prop} {a b c : α} (h1 : Rt R a b) (h2 : Rt R b c) : Rt R a c := by
  induction h2 with
  | refl => exact h1
  | tail _ h ih => exact Rt.tail ih h

theorem Rt.single {α : Type} {R : α → α → Prop} {a b : α} (h : R a b) : Rt R a b := Rt.tail (Rt.refl a) h

/-- The odometer record at digits `(π, d)` of a cycle started at an initial record. -/
def ORec.at (o : ORec) (π d : Nat) : ORec :=
  { o with d := d, z := 0, k := π + 1, m := o.z + o.k - 1 + o.m - π }

def NI (a b : ORec) : Prop := a.next = Sum.inl b

theorem at_d (o : ORec) (π d : Nat) (h0 : o.z = 0) (h1 : o.k = 1) (hd : d + 1 < o.r) (hπ : π ≤ o.m) :
    NI (o.at π d) (o.at π (d + 1)) := by
  unfold NI ORec.next ORec.at
  simp only
  rw [if_pos hd]

theorem at_k (o : ORec) (π : Nat) (h0 : o.z = 0) (h1 : o.k = 1) (hd : 1 ≤ o.r) (hπ : π + 1 ≤ o.m) :
    NI (o.at π (o.r - 1)) (o.at (π + 1) 0) := by
  unfold NI ORec.next ORec.at
  simp only
  rw [if_neg (by omega), if_pos (by omega)]
  simp [h0, h1]
  omega

theorem head_reach (o : ORec) (h0 : o.z = 0) (h1 : o.k = 1) (hd0 : o.d = 0) (hr : 1 ≤ o.r) :
    ∀ π d, π ≤ o.m → d < o.r → Rt NI o (o.at π d) := by
  have e0 : o = o.at 0 0 := by
    cases o
    simp_all [ORec.at]
  intro π
  induction π with
  | zero =>
    intro d _ hdr
    induction d with
    | zero => rw [← e0]; exact Rt.refl _
    | succ d ih => exact Rt.tail (ih (by omega)) (at_d o 0 d h0 h1 (by omega) (by omega))
  | succ π ih =>
    intro d hπ hdr
    have hA : Rt NI o (o.at π (o.r - 1)) := ih _ (by omega) (by omega)
    have hB : Rt NI o (o.at (π + 1) 0) := Rt.tail hA (at_k o π h0 h1 hr (by omega))
    induction d with
    | zero => exact hB
    | succ d ih2 => exact Rt.tail (ih2 (by omega)) (at_d o (π + 1) d h0 h1 (by omega) hπ)

def OS (a b : List ORec) : Prop := odoStepR a = some b

theorem lift_head (S : List ORec) {a b : ORec} (h : Rt NI a b) : Rt OS (a :: S) (b :: S) := by
  induction h with
  | refl => exact Rt.refl _
  | tail _ hn ih =>
    refine Rt.tail ih ?_
    unfold OS odoStepR
    unfold NI at hn
    rw [hn]

theorem cyc (o : ORec) (h0 : o.z = 0) (h1 : o.k = 1) (hd0 : o.d = 0) (hr : 1 ≤ o.r) (S S2 : List ORec)
    (hS : odoStepR S = some S2) : Rt OS (o :: S) (o :: S2) := by
  have h := lift_head S (head_reach o h0 h1 hd0 hr o.m (o.r - 1) (Nat.le_refl _) (by omega))
  refine h.tail ?_
  unfold OS odoStepR
  have : (o.at o.m (o.r - 1)).next = Sum.inr o := by
    unfold ORec.next ORec.at
    simp only
    rw [if_neg (by omega), if_neg (by simp [h0, h1])]
    cases o
    simp_all
  rw [this]
  simp [hS]

def Fit : List ORec → List Nat → List Nat → Prop
  | [], [], [] => True
  | o :: os, π :: πs, d :: ds => π ≤ o.m ∧ d < o.r ∧ Fit os πs ds
  | _, _, _ => False

def setD : List ORec → List Nat → List Nat → List ORec
  | o :: os, π :: πs, d :: ds => o.at π d :: setD os πs ds
  | _, _, _ => []

theorem cover : ∀ (os : List ORec) (πs ds : List Nat),
    (∀ x ∈ os, x.z = 0 ∧ x.k = 1 ∧ x.d = 0 ∧ 1 ≤ x.r) → Fit os πs ds → Rt OS os (setD os πs ds)
  | [], πs, ds, _, h => by
    cases πs <;> cases ds <;> simp [Fit] at h
    exact Rt.refl _
  | o :: os, πs, ds, hI, h => by
    cases πs with
    | nil => simp [Fit] at h
    | cons π πs =>
      cases ds with
      | nil => simp [Fit] at h
      | cons d ds =>
        obtain ⟨h1, h2, h3⟩ := h
        obtain ⟨a0, a1, a2, a3⟩ := hI o (by simp)
        have ih := cover os πs ds (fun x hx => hI x (by simp [hx])) h3
        have hT : Rt OS (o :: os) (o :: setD os πs ds) := by
          clear h1 h2 h3
          generalize setD os πs ds = T at ih
          induction ih with
          | refl => exact Rt.refl _
          | tail _ hs ih2 => exact ih2.trans (cyc o a0 a1 a2 a3 _ _ hs)
        have hH := lift_head (setD os πs ds) (head_reach o a0 a1 a2 a3 π d h1 h2)
        exact hT.trans hH


theorem Rt.det_step {α : Type} {R : α → α → Prop} (hf : ∀ a b c, R a b → R a c → b = c) {b x e : α}
    (hx : R b x) (h : Rt R b e) : b = e ∨ Rt R x e := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hr ih =>
    rcases ih with rfl | ih
    · exact Or.inr (by rw [hf _ _ _ hr hx]; exact Rt.refl _)
    · exact Or.inr (Rt.tail ih hr)

/-- Along a deterministic step relation, a state reachable from `a` precedes a terminal state reachable from `a`. -/
theorem Rt.det_term {α : Type} {R : α → α → Prop} (hf : ∀ a b c, R a b → R a c → b = c) {a x e : α}
    (hx : Rt R a x) (he : Rt R a e) (ht : ∀ y, ¬ R e y) : Rt R x e := by
  induction hx with
  | refl => exact he
  | tail _ hr ih =>
    rcases Rt.det_step hf hr ih with rfl | h
    · exact absurd hr (ht _)
    · exact h

theorem OS_det : ∀ a b c, OS a b → OS a c → b = c := by
  intro a b c h1 h2
  unfold OS at h1 h2
  rw [h1] at h2
  exact Option.some.inj h2

/-- Coverage plus determinism: if the odometer from an initial list terminates, every in-range digit assignment is visited. -/
theorem odo_all_visited (os e : List ORec) (hI : ∀ x ∈ os, x.z = 0 ∧ x.k = 1 ∧ x.d = 0 ∧ 1 ≤ x.r)
    (he : Rt OS os e) (ht : odoStepR e = none) (πs ds : List Nat) (hF : Fit os πs ds) :
    Rt OS (setD os πs ds) e ∧ Rt OS os (setD os πs ds) :=
  ⟨Rt.det_term OS_det (cover os πs ds hI hF) he (fun y hy => by unfold OS at hy; rw [ht] at hy; simp at hy),
    cover os πs ds hI hF⟩


/-- Compare clause of the `O = 3` records against a list of node values. -/
def CmpE : List VR → List Nat → Prop
  | [], _ => True
  | _ :: _, [] => True
  | x :: xs, v :: vl => (x.O = 3 → ∃ z, 1 ≤ v + 1 ∧ x.E = fld (v + 1 + z) (v + 1)) ∧ CmpE xs vl

theorem CmpE_congr : ∀ (xs ys : List VR) (vl : List Nat), xs.length = ys.length →
    (∀ (i : Nat) (x y : VR), xs[i]? = some x → ys[i]? = some y → x.O = y.O ∧ x.E = y.E) → (CmpE xs vl ↔ CmpE ys vl)
  | [], [], _, _, _ => Iff.rfl
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | x :: xs, y :: ys, [], _, _ => by simp [CmpE]
  | x :: xs, y :: ys, v :: vl, hl, h => by
    have h0 := h 0 x y (by simp) (by simp)
    have ih := CmpE_congr xs ys vl (by simpa using hl) (fun i a b ha hb => h (i + 1) a b (by simpa using ha) (by simpa using hb))
    simp only [CmpE, h0.1, h0.2, ih]

theorem passCmp_iff (p t N : Nat) (πs ds vals : List Nat) (hp : 0 < p) (hV : ValsOk p t N πs ds vals) :
    ∀ (n j : Nat) (c : VR) (vs : List VR) (r : Nat), vs.length = n → j + n + 1 = N →
      ColInv p t j πs ds vals (c :: vs) → r = c.k - 1 →
      (PassCmp n r vs ↔ CmpE vs ((List.range n).map fun i => vals.getD (j + i + 1) 0)) := by
  intro n
  induction n with
  | zero =>
    intro j c vs r hl hN hI hr
    have hvs : vs = [] := List.length_eq_zero_iff.1 hl
    subst hvs
    simp [PassCmp, CmpE]
  | succ n ih =>
    intro j c vs r hl hN hI hr
    obtain ⟨v0, vs', rfl⟩ : ∃ v0 vs', vs = v0 :: vs' := by
      cases vs with
      | nil => simp at hl
      | cons a b => exact ⟨a, b, rfl⟩
    have hrj : r = vals.getD j 0 := by
      rw [hr]; exact cursor_val p t N πs ds vals hV j c _ (by omega) hI
    have h0 := hI 1 v0 (by simp)
    simp only [show ¬ ((1:Nat) = 0) from by decide, if_false] at h0
    have hhead := recI_head p _ j _ _ vals v0 r hp h0 hrj
    have hI' : ColInv p t (j + 1) πs ds vals
        (VR.curG (incVisN r v0) :: (vs'.map (visN r)).map VR.dec) := by
      intro idx x hx
      cases idx with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        have e : (if (0:Nat) = 0 then (if j + 1 = 0 then 0 else vals.getD (j + 1 - 1) 0) else 0) = r := by
          simp [hrj]
        rw [e]; exact hhead
      | succ idx =>
        simp only [List.getElem?_cons_succ, List.getElem?_map, Option.map_eq_some_iff] at hx
        obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := hx
        have hz' : (c :: v0 :: vs')[idx + 2]? = some z := by simpa using hz
        have h1 := hI (idx + 2) z hz'
        have e : j + 1 + (idx + 1) = j + (idx + 2) := by omega
        rw [e]
        simp only [show ¬ (idx + 2 = 0) from by omega, if_false] at h1
        simp only [show ¬ (idx + 1 = 0) from by omega, if_false]
        exact recI_tail p _ j _ _ vals z r hp h1 hrj
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := curG_f (incVisN r v0) (incVisN_val r v0 h0.1).1
    have df := dec_fields' (incVisN r v0)
    have hr' : (incVisN r v0).k - 1 = (VR.curG (incVisN r v0)).k - 1 := by rw [g3, df.2.2.1]
    have hl' : ((vs'.map (visN r)).map VR.dec).length = n := by simp at hl ⊢; omega
    have IH := ih (j + 1) (VR.curG (incVisN r v0)) _ ((incVisN r v0).k - 1) hl' (by omega) hI' hr'
    have iv := incVisN_val r v0 h0.1
    -- value of the head
    have hval : (incVisN r v0).k - 1 = vals.getD (j + 1) 0 := by
      have := cursor_val p t N πs ds vals hV (j + 1) _ _ (by omega) hI'
      rw [hr'] ; exact this
    have hk1 : 1 ≤ (incVisN r v0).k := iv.1.1.k1 |> fun h => by omega
    have hkv : (incVisN r v0).k = vals.getD (j + 1) 0 + 1 := by omega
    simp only [PassCmp, stepN_cons]
    rw [IH]
    have hmap : CmpE (vs'.map fun x => x) ((List.range n).map fun i => vals.getD (j + 1 + i + 1) 0) ↔
        CmpE ((vs'.map (visN r)).map VR.dec) ((List.range n).map fun i => vals.getD (j + 1 + i + 1) 0) := by
      apply CmpE_congr
      · simp
      · intro i x y hx hy
        simp only [List.getElem?_map, Option.map_eq_some_iff] at hx hy
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨b, ⟨c', hc', rfl⟩, rfl⟩ := hy
        have : a = c' := by rw [ha] at hc'; exact Option.some.inj hc'
        subst this
        have hv := hI (i + 2) a (by simpa using ha)
        have vv := visIter r a (by exact hv.1)
        refine ⟨by simp [(dec_EO _).2, vv.2.2.2.2.2.2.1], by simp [(dec_EO _).1, vv.2.2.2.2.2.2.2.1]⟩
    rw [List.range_succ_eq_map, List.map_cons, CmpE]
    have hrange : (List.map (fun i => vals.getD (j + i + 1) 0) (List.map Nat.succ (List.range n))) =
        List.map (fun i => vals.getD (j + 1 + i + 1) 0) (List.range n) := by
      rw [List.map_map]; apply List.map_congr_left; intro i _
      simp only [Function.comp]; congr 1; omega
    rw [hrange, List.map_id'] at *
    rw [← hmap]
    obtain ⟨_, _, _, _, _, _, hO, hE, _, _⟩ := iv
    rw [hO, hE, hkv]


/-- Contribution of a finished record to the `S` register: `r * n` for output records. -/
def ctrS (t : VR × Nat × Nat) : Nat := if t.1.O = 2 then 0 else t.2.1 * t.1.n

theorem outP_val (c : VR) (r : Nat) (p : Nat × Nat) (hp : 1 ≤ p.2) :
    (outP c r p).1 = (p.1 + (if c.O = 2 then 0 else r * c.n)) % (p.1 + p.2) := by
  unfold outP
  split
  · rename_i h; rw [Nat.add_zero]; exact (Nat.mod_eq_of_lt (by omega)).symm
  · exact (sAdv_val _ p hp).2.2

theorem loopRun_pval : ∀ (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat), 1 ≤ p.2 →
    (loopRun n c vs r s p).p'.1 =
      (p.1 + ((loopRun n c vs r s p).cs.map ctrS).sum) % (p.1 + p.2)
  | 0, c, vs, r, s, p, hp => by
    simp [loopRun]; exact (Nat.mod_eq_of_lt (by omega)).symm
  | n + 1, c, vs, r, s, p, hp => by
    unfold loopRun
    split
    · simp; exact (Nat.mod_eq_of_lt (by omega)).symm
    · rename_i w ws hw
      have ih := loopRun_pval n w.curG (ws.map VR.dec) (w.k - 1) (w.w - w.k) (outP c r p) (outP_pos c r p hp)
      have hs := outP_sum c r p hp
      have hv := outP_val c r p hp
      simp only [List.map_cons, List.sum_cons]
      rw [ih, hs, hv, Nat.mod_add_mod]
      have hO : (outRec c r).O = c.O := by unfold outRec; split <;> rfl
      have hn : (outRec c r).n = c.n := by unfold outRec; split <;> rfl
      simp only [ctrS, hO, hn]
      congr 1; omega

theorem passPOf_val (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat) (hp : 1 ≤ p.2) :
    (passPOf n c vs r s p).1 = (p.1 + ((passCsOf n c vs r s p).map ctrS).sum) % (p.1 + p.2) := by
  have h1 := loopRun_pval n c vs r s p hp
  have h2 := loopRun_psum n c vs r s p hp
  have h3 := outP_val (loopRun n c vs r s p).c' (loopRun n c vs r s p).r' (loopRun n c vs r s p).p' h2.1
  unfold passPOf; rw [h3, h2.2, h1, Nat.mod_add_mod]
  unfold passCsOf
  have hO : (outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r').O = (loopRun n c vs r s p).c'.O := by
    unfold outRec; split <;> rfl
  have hn : (outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r').n = (loopRun n c vs r s p).c'.n := by
    unfold outRec; split <;> rfl
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ctrS, hO, hn]
  congr 1; omega

theorem loopRs (p t N : Nat) (πs ds vals : List Nat) (hp : 0 < p) (hV : ValsOk p t N πs ds vals) :
    ∀ (n j : Nat) (c : VR) (vs : List VR) (r s : Nat) (pp : Nat × Nat), vs.length = n → j + n + 1 = N →
      ColInv p t j πs ds vals (c :: vs) → r = c.k - 1 →
      (loopRun n c vs r s pp).cs.map (fun x => x.1.k - 1) = (List.range n).map (fun i => vals.getD (j + i) 0) ∧
      (loopRun n c vs r s pp).c'.k - 1 = vals.getD (j + n) 0 ∧
      (loopRun n c vs r s pp).cs.map (fun x => x.2.1) = (List.range n).map (fun i => vals.getD (j + i) 0) ∧
      (loopRun n c vs r s pp).r' = vals.getD (j + n) 0 := by
  intro n
  induction n with
  | zero =>
    intro j c vs r s pp hl hN hI hr
    have hvs : vs = [] := List.length_eq_zero_iff.1 hl
    subst hvs
    have hcv := cursor_val p t N πs ds vals hV j c [] (by omega) hI
    simp only [loopRun, List.range_zero, List.map_nil, true_and, Nat.add_zero]
    exact ⟨hcv, by rw [hr]; exact hcv⟩
  | succ n ih =>
    intro j c vs r s pp hl hN hI hr
    obtain ⟨v0, vs', rfl⟩ : ∃ v0 vs', vs = v0 :: vs' := by
      cases vs with
      | nil => simp at hl
      | cons a b => exact ⟨a, b, rfl⟩
    have hrj : r = vals.getD j 0 := by
      rw [hr]; exact cursor_val p t N πs ds vals hV j c _ (by omega) hI
    have h0 := hI 1 v0 (by simp)
    simp only [show ¬ ((1:Nat) = 0) from by decide, if_false] at h0
    have hhead := recI_head p _ j _ _ vals v0 r hp h0 hrj
    have hI' : ColInv p t (j + 1) πs ds vals
        (VR.curG (incVisN r v0) :: (vs'.map (visN r)).map VR.dec) := by
      intro idx x hx
      cases idx with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        have e : (if (0:Nat) = 0 then (if j + 1 = 0 then 0 else vals.getD (j + 1 - 1) 0) else 0) = r := by
          simp [hrj]
        rw [e]; exact hhead
      | succ idx =>
        simp only [List.getElem?_cons_succ, List.getElem?_map, Option.map_eq_some_iff] at hx
        obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := hx
        have hz' : (c :: v0 :: vs')[idx + 2]? = some z := by simpa using hz
        have h1 := hI (idx + 2) z hz'
        have e : j + 1 + (idx + 1) = j + (idx + 2) := by omega
        rw [e]
        simp only [show ¬ (idx + 2 = 0) from by omega, if_false] at h1
        simp only [show ¬ (idx + 1 = 0) from by omega, if_false]
        exact recI_tail p _ j _ _ vals z r hp h1 hrj
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := curG_f (incVisN r v0) (incVisN_val r v0 h0.1).1
    have df := dec_fields' (incVisN r v0)
    have hr' : (incVisN r v0).k - 1 = (VR.curG (incVisN r v0)).k - 1 := by rw [g3, df.2.2.1]
    have hl' : ((vs'.map (visN r)).map VR.dec).length = n := by simp at hl ⊢; omega
    have IH := ih (j + 1) (VR.curG (incVisN r v0)) _ ((incVisN r v0).k - 1) ((incVisN r v0).w - (incVisN r v0).k)
      (outP c r pp) hl' (by omega) hI' hr'
    have hk : (outRec c r).k = c.k := by unfold outRec; split <;> rfl
    simp only [loopRun, stepN_cons]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [List.range_succ_eq_map, List.map_cons, List.map_cons]
      refine List.cons_eq_cons.2 ⟨?_, ?_⟩
      · simp only [hk, Nat.add_zero]; rw [← hr]; exact hrj.symm ▸ rfl
      · rw [IH.1, List.map_map]
        apply List.map_congr_left
        intro i _
        simp only [Function.comp]
        congr 1; omega
    · have := IH.2.1
      rw [this]; congr 1; omega
    · rw [List.range_succ_eq_map, List.map_cons, List.map_cons]
      refine List.cons_eq_cons.2 ⟨?_, ?_⟩
      · simp only [Nat.add_zero]; exact hrj
      · rw [IH.2.2.1, List.map_map]
        apply List.map_congr_left
        intro i _
        simp only [Function.comp]
        congr 1; omega
    · have := IH.2.2.2
      rw [this]; congr 1; omega




/-- `Σ` of `value * digit` over the output records. -/
def SumOD : List DG → List Nat → Nat
  | g :: gs, v :: vl => (if g.2.2.2.2.2 = 2 then 0 else v * g.1) + SumOD gs vl
  | _, _ => 0

theorem ctrS_sumOD : ∀ ts : List (VR × Nat × Nat),
    (ts.map ctrS).sum = SumOD (ts.map fun t => t.1.dg) (ts.map fun t => t.2.1)
  | [] => rfl
  | t :: ts => by
    simp only [List.map_cons, List.sum_cons, SumOD, ctrS, VR.dg, ctrS_sumOD ts]

theorem passCs_sum (p t N : Nat) (πs ds vals : List Nat) (hp : 0 < p) (hV : ValsOk p t N πs ds vals)
    (n j : Nat) (c : VR) (vs : List VR) (r s : Nat) (pp : Nat × Nat) (hl : vs.length = n) (hN : j + n + 1 = N)
    (hI : ColInv p t j πs ds vals (c :: vs)) (hr : r = c.k - 1) (hc : c.m = 0) (hvs : ∀ x ∈ vs, x.m = 0) :
    ((passCsOf n c vs r s pp).map ctrS).sum =
      SumOD ((c :: vs).map VR.dg) ((List.range (n + 1)).map fun i => vals.getD (j + i) 0) := by
  have h1 := dg_runAll_pos n c vs r s pp hc hvs hl
  have h2 := loopRs p t N πs ds vals hp hV n j c vs r s pp hl hN hI hr
  rw [ctrS_sumOD]
  unfold passCsOf
  have h3 : ((loopRun n c vs r s pp).cs ++ [(outRec (loopRun n c vs r s pp).c' (loopRun n c vs r s pp).r',
        (loopRun n c vs r s pp).r', (loopRun n c vs r s pp).s')]).map (fun t => t.2.1) =
      (List.range (n + 1)).map fun i => vals.getD (j + i) 0 := by
    rw [List.map_append, h2.2.2.1, List.range_succ, List.map_append]
    simp [h2.2.2.2]
  rw [h3, h1]


/-- Final `E` register of a finished record with node value `r`. -/
def Efin (v : VR) (r : Nat) : List Nat :=
  if v.O = 2 then v.E else fld v.E.length (eAdv v.E.length (r * v.n) 1)

def finE : List VR → List Nat → List (List Nat)
  | v :: vs, r :: rs => Efin v r :: finE vs rs
  | _, _ => []

def KEq (v v' : VR) : Prop :=
  v.O = v'.O ∧ v.n = v'.n ∧ v.E.length = v'.E.length ∧ (v.O = 2 → v.E = v'.E)

theorem Efin_congr (v v' : VR) (h : KEq v v') (r : Nat) : Efin v r = Efin v' r := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold Efin
  by_cases hO : v.O = 2
  · rw [if_pos hO, if_pos (h1 ▸ hO), h4 hO]
  · rw [if_neg hO, if_neg (h1 ▸ hO), h2, h3]

theorem finE_congr : ∀ (vs vs' : List VR) (rs : List Nat), vs.length = vs'.length →
    (∀ (i : Nat) (a b : VR), vs[i]? = some a → vs'[i]? = some b → KEq a b) → finE vs rs = finE vs' rs
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | a :: vs, b :: vs', [], _, _ => by simp [finE]
  | a :: vs, b :: vs', r :: rs, hl, h => by
    simp only [finE]
    rw [Efin_congr a b (h 0 a b (by simp) (by simp)) r,
      finE_congr vs vs' rs (by simpa using hl) (fun i x y hx hy => h (i + 1) x y (by simpa using hx) (by simpa using hy))]

theorem outRec_Efin (c : VR) (r : Nat) (hl : 1 ≤ c.E.length) (hO23 : c.O = 2 ∨ c.O = 3) (hE : c.O = 3 → c.E = fld c.E.length 1) :
    (outRec c r).E = Efin c r := by
  unfold outRec Efin
  by_cases hO : c.O = 2
  · simp [hO]
  · simp only [if_neg hO]
    have hc : c.E.count 3 = 1 := by
      have h3 : c.O = 3 := by omega
      rw [hE h3]; exact count3_fld' _ _ hl |>.trans rfl
    rw [hc]


theorem KEq_trans {a b c : VR} (h1 : KEq a b) (h2 : KEq b c) : KEq a c :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1, fun h => (h1.2.2.2 h).trans (h2.2.2.2 (h1.1 ▸ h))⟩

theorem curG_KEq (w : VR) (hl : 1 ≤ w.E.length) : KEq w.curG w := by
  have h1 := dec_EO w
  have h2 := dec_fields' w
  unfold VR.curG VR.cur
  by_cases hO : w.O = 3
  · simp only [if_pos hO]
    refine ⟨by simp [h1.2], by simp [h2.1], ?_, by simp [h1.2]; intro h; omega⟩
    simp [fld, h1.1]; omega
  · simp only [if_neg hO]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [h1.1, h1.2, h2.1]

theorem incVis_KEq (r : Nat) (v : VR) (h : VI v) : KEq (incVisN r v) v := by
  obtain ⟨_, _, _, h3, _, _, h7, h8, _, _⟩ := incVisN_val r v h
  exact ⟨h7, h3, by rw [h8], fun _ => h8⟩

theorem decVis_KEq (r : Nat) (v : VR) (h : VI v) : KEq (VR.dec (visN r v)) v := by
  obtain ⟨_, _, _, h3, _, _, h7, h8, _, _⟩ := visIter r v h
  have h1 := dec_EO (visN r v)
  have h2 := dec_fields' (visN r v)
  exact ⟨by rw [h1.2, h7], by rw [h2.1, h3], by rw [h1.1, h8], fun _ => by rw [h1.1, h8]⟩

theorem loopEs : ∀ (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (pp : Nat × Nat), vs.length = n → VI c →
    (∀ x ∈ vs, VI x) → (c.O = 3 → c.E = fld c.E.length 1) →
    (loopRun n c vs r s pp).cs.map (fun x => x.1.E) =
      finE (c :: vs) ((loopRun n c vs r s pp).cs.map (fun x => x.2.1))
  | 0, c, vs, r, s, pp, _, _, _, _ => by simp [loopRun, finE]
  | n + 1, c, vs, r, s, pp, hl, hc, hvs, hcE => by
    obtain ⟨v0, vs', rfl⟩ : ∃ v0 vs', vs = v0 :: vs' := by
      cases vs with
      | nil => simp at hl
      | cons a b => exact ⟨a, b, rfl⟩
    have hv0 : VI v0 := hvs v0 (by simp)
    have hvs' : ∀ x ∈ vs', VI x := fun x hx => hvs x (by simp [hx])
    have hI1 := (incVisN_val r v0 hv0).1
    have hcg := curG_f _ hI1
    have hl' : ((vs'.map (visN r)).map VR.dec).length = n := by simp at hl ⊢; omega
    have hvs'' : ∀ x ∈ (vs'.map (visN r)).map VR.dec, VI x := by
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := hx
      have := (visIter r z (hvs' z hz)).1
      exact ⟨(visN r z).dec_ok this.1, by
        have := dec_fields' (visN r z); rw [this.2.1]; exact (visIter r z (hvs' z hz)).1.2⟩
    have hk0 := curG_KEq (incVisN r v0) (by have := hI1.1.Elen; omega)
    have IH := loopEs n (VR.curG (incVisN r v0)) _ ((incVisN r v0).k - 1) ((incVisN r v0).w - (incVisN r v0).k)
      (outP c r pp) hl' hcg.1 hvs'' (by
        intro h3
        have hO3 : (incVisN r v0).O = 3 := by rw [← hk0.1]; exact h3
        have e1 : (incVisN r v0).curG.E = fld (incVisN r v0).E.length 1 := by simp [VR.curG, VR.cur, hO3, VR.dec]
        have hl1 : 1 ≤ (incVisN r v0).E.length := by have := hI1.1.Elen; omega
        rw [e1, fld_len _ _ hl1])
    simp only [loopRun, stepN_cons]
    simp only [List.map_cons, finE]
    refine List.cons_eq_cons.2 ⟨?_, ?_⟩
    · exact outRec_Efin c r (by have := hc.1.Elen; omega) (by have := hc.1.O; simpa using this) hcE
    · rw [IH]
      apply finE_congr
      · simp [hl']
      · intro i a b ha hb
        cases i with
        | zero =>
          simp at ha hb; subst ha; subst hb
          exact KEq_trans hk0 (incVis_KEq r v0 hv0)
        | succ i =>
          simp only [List.getElem?_cons_succ, List.getElem?_map, Option.map_eq_some_iff] at ha hb
          obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := ha
          have hb' : vs'[i]? = some b := by simpa using hb
          have hzb : z = b := Option.some.inj (hz.symm.trans hb')
          subst hzb
          exact decVis_KEq r z (hvs' z (List.mem_of_getElem? hz))


theorem decRecs_getD : ∀ (πs ds : List Nat) (i : Nat), i < πs.length → πs.length = ds.length →
    (decRecs πs ds).getD i (none, 0) = (ptrOf (πs.getD i 0), ds.getD i 0)
  | [], _, i, h, _ => by simp at h
  | π :: πs, [], i, _, h => by simp at h
  | π :: πs, d :: ds, 0, _, _ => by simp [decRecs]
  | π :: πs, d :: ds, i + 1, h, hl => by
    simp only [decRecs, List.getD_cons_succ]
    exact decRecs_getD πs ds i (by simpa using h) (by simpa using hl)

theorem decRecs_length : ∀ (πs ds : List Nat), πs.length = ds.length → (decRecs πs ds).length = πs.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | π :: πs, d :: ds, h => by simp [decRecs, decRecs_length πs ds (by simpa using h)]

theorem valsOk_decRecs (p t : Nat) (πs ds : List Nat) (hl : πs.length = ds.length) :
    ValsOk p t πs.length πs ds (valsAux t p 0 (decRecs πs ds) []) := by
  intro i hi
  have := valsAux_get t p (decRecs πs ds) 0 [] rfl i (Nat.zero_le _) (by rw [decRecs_length πs ds hl]; omega)
  rw [this, Nat.sub_zero, decRecs_getD πs ds i hi hl]


/-- Reference passes `t, t+1, …` (`k` of them) starting from register `E`. -/
def evalFrom (n p : Nat) (recs : List Rec) : Nat → Nat → List Nat → Option (List Nat)
  | _, 0, E => some E
  | t, k + 1, E => (evalPass n p recs t E).bind (evalFrom n p recs (t + 1) k)

theorem fold_evalFrom (n p : Nat) (recs : List Rec) : ∀ (k t : Nat) (st : Option (List Nat)),
    (List.range' t k).foldl (fun st u => st.bind fun E => evalPass n p recs u E) st =
      st.bind (evalFrom n p recs t k)
  | 0, t, st => by cases st <;> simp [evalFrom]
  | k + 1, t, st => by
    rw [List.range'_succ, List.foldl_cons, fold_evalFrom n p recs k (t + 1)]
    cases st <;> simp [evalFrom]

theorem evalC_eq (n p : Nat) (recs : List Rec) :
    evalC n p recs = (evalFrom n p recs 0 n (List.replicate n 1)).isSome := by
  unfold evalC
  rw [List.range_eq_range', fold_evalFrom]
  rfl



/-- Start record of a pass: digit signature, pass flag `x`, E-register value `e`. -/
def mkStart (g : DG) (x e : Nat) : VR :=
  { F := 2, O := g.2.2.2.2.2, P := x, w := g.2.2.2.2.1, k := if x = 3 then 2 else 1,
    E := fld g.2.2.2.2.1 (e + 1), m := 0, n := g.1, s := g.2.1, a := 0, c := g.2.2.1, t := g.2.2.2.1 }

theorem vrD_mkStart (g : DG) (x : Nat) (hw : 2 ≤ g.2.2.2.2.1) : vrD g x = mkStart g x 1 := by
  unfold vrD mkStart fld
  obtain ⟨u, hu⟩ : ∃ u, g.2.2.2.2.1 = u + 2 := ⟨g.2.2.2.2.1 - 2, by omega⟩
  rw [hu]; simp [List.replicate_succ]

theorem mkStart_ok (g : DG) (x e : Nat) (hx : x = 2 ∨ x = 3) (hO : g.2.2.2.2.2 = 2 ∨ g.2.2.2.2.2 = 3)
    (hw : 2 ≤ g.2.2.2.2.1) (he : e + 1 ≤ g.2.2.2.2.1) : (mkStart g x e).Ok := by
  refine { F := ?_, O := ?_, P := ?_, k1 := ?_, kw := ?_, E := ?_, Elen := ?_, Elw := ?_ } <;>
    simp only [mkStart]
  · simp
  · rcases hO with h | h <;> simp [h]
  · rcases hx with h | h <;> simp [h]
  · split <;> omega
  · split <;> omega
  · exact fld_bits _ _
  · rw [fld_len _ _ he]; exact hw
  · rw [fld_len _ _ he]


def fl (t i : Nat) : Nat := if i = t then 3 else 2

def mkSL (t : Nat) : Nat → List DG → List Nat → List VR
  | i, g :: gs, e :: es => mkStart g (fl t i) e :: mkSL t (i + 1) gs es
  | _, _, _ => []

/-- Well-formedness of the digit signatures and E values of a pass. -/
def DOk (p : Nat) (D : List DG) (es : List Nat) : Prop :=
  D.length = es.length ∧ 2 ≤ p ∧ ∀ (i : Nat) (g : DG) (e : Nat), D[i]? = some g → es[i]? = some e →
    g.2.2.2.2.1 = p ∧ (g.2.2.2.2.2 = 2 ∨ g.2.2.2.2.2 = 3) ∧ e < p

theorem mkSL_length : ∀ (t i : Nat) (D : List DG) (es : List Nat), D.length = es.length →
    (mkSL t i D es).length = D.length
  | t, i, [], [], _ => rfl
  | t, i, [], _ :: _, h => by simp at h
  | t, i, _ :: _, [], h => by simp at h
  | t, i, g :: gs, e :: es, h => by simp [mkSL, mkSL_length t (i + 1) gs es (by simpa using h)]

theorem mkSL_get : ∀ (t i : Nat) (D : List DG) (es : List Nat) (idx : Nat) (y : VR),
    (mkSL t i D es)[idx]? = some y → ∃ g e, D[idx]? = some g ∧ es[idx]? = some e ∧ y = mkStart g (fl t (i + idx)) e
  | t, i, [], _, idx, y, h => by simp [mkSL] at h
  | t, i, _ :: _, [], idx, y, h => by simp [mkSL] at h
  | t, i, g :: gs, e :: es, 0, y, h => by
    simp [mkSL] at h
    exact ⟨g, e, by simp, by simp, by simp [← h]⟩
  | t, i, g :: gs, e :: es, idx + 1, y, h => by
    simp only [mkSL, List.getElem?_cons_succ] at h
    obtain ⟨g', e', h1, h2, h3⟩ := mkSL_get t (i + 1) gs es idx y h
    exact ⟨g', e', by simpa using h1, by simpa using h2, by rw [h3]; congr 2; omega⟩

theorem mkStart_start (p : Nat) (g : DG) (x e : Nat) (hx : x = 2 ∨ x = 3) (hO : g.2.2.2.2.2 = 2 ∨ g.2.2.2.2.2 = 3)
    (hw : g.2.2.2.2.1 = p) (hp : 2 ≤ p) (he : e < p) :
    StartRec p (if x = 3 then 1 else 0) g.2.2.1 g.1 (mkStart g x e) := by
  refine ⟨⟨mkStart_ok g x e hx hO (by omega) (by omega), rfl⟩, hw, rfl, rfl, by simp [mkStart], ?_⟩
  simp only [mkStart]; split <;> simp_all

theorem mkSL_startRec (p t : Nat) (D : List DG) (es : List Nat) (hD : DOk p D es) :
    ∀ idx y, (mkSL t 0 D es)[idx]? = some y →
      StartRec p (if idx = t then 1 else 0) ((D.map fun g => g.2.2.1).getD idx 0) ((D.map fun g => g.1).getD idx 0) y := by
  intro idx y hy
  obtain ⟨g, e, h1, h2, rfl⟩ := mkSL_get t 0 D es idx y hy
  obtain ⟨hw, hO, he⟩ := hD.2.2 idx g e h1 h2
  have hx : fl t (0 + idx) = 2 ∨ fl t (0 + idx) = 3 := by unfold fl; split <;> simp
  have := mkStart_start p g (fl t (0 + idx)) e hx hO hw hD.2.1 he
  have e1 : (D.map fun g => g.2.2.1).getD idx 0 = g.2.2.1 := by simp [List.getD_eq_getElem?_getD, h1]
  have e2 : (D.map fun g => g.1).getD idx 0 = g.1 := by simp [List.getD_eq_getElem?_getD, h1]
  rw [e1, e2]
  unfold fl at this ⊢
  simpa using this


/-- Full success of the remaining passes, from the semantic description of the start records. -/
def FOkS (m n : Nat) (D : List DG) (es : List Nat) (t : Nat) (L : List Nat) (S : Nat) : Prop :=
  match mkSL t 0 D es with
  | [] => False
  | y0 :: ys => FOk m n y0.curG (ys.map VR.dec) (y0.k - 1) (y0.w - y0.k) (0, S) t L

theorem mkSL_init : ∀ (i : Nat) (gs : List DG), (∀ g ∈ gs, 2 ≤ g.2.2.2.2.1) →
    mkSL 0 (i + 1) gs (List.replicate gs.length 1) = gs.map fun x => vrD x 2
  | i, [], _ => rfl
  | i, g :: gs, h => by
    simp only [List.length_cons, List.replicate_succ, mkSL, List.map_cons]
    rw [mkSL_init (i + 1) gs (fun x hx => h x (by simp [hx])), vrD_mkStart g 2 (h g (by simp))]
    simp [fl]

theorem AOkD_eq (m n : Nat) (D : List DG) (s : Nat) (hw : ∀ g ∈ D, 2 ≤ g.2.2.2.2.1) :
    AOkD m n D s ↔ FOkS m n D (List.replicate D.length 1) 0 (List.replicate n 2) s := by
  cases D with
  | nil => simp [AOkD, FOkS, mkSL]
  | cons g gs =>
    have h1 := mkSL_init 0 gs (fun x hx => hw x (by simp [hx]))
    have h0 : vrD g 3 = mkStart g 3 1 := vrD_mkStart g 3 (hw g (by simp))
    simp only [AOkD, FOkS, List.length_cons, List.replicate_succ, mkSL, h1]
    simp only [fl, if_true, h0]



theorem passCsOf_zero (c : VR) (r s : Nat) (p : Nat × Nat) :
    passCsOf 0 c [] r s p = [(outRec c r, r, s)] := by
  simp [passCsOf, loopRun]

theorem passCsOf_succ (n : Nat) (v0 : VR) (vs' : List VR) (c : VR) (r s : Nat) (p : Nat × Nat) :
    passCsOf (n + 1) c (v0 :: vs') r s p =
      (outRec c r, r, s) ::
        passCsOf n (incVisN r v0).curG ((vs'.map (visN r)).map VR.dec) ((incVisN r v0).k - 1)
          ((incVisN r v0).w - (incVisN r v0).k) (outP c r p) := by
  unfold passCsOf
  simp only [loopRun, stepN_cons]
  simp

theorem passEs : ∀ (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (pp : Nat × Nat), vs.length = n → VI c →
    (∀ x ∈ vs, VI x) → (c.O = 3 → c.E = fld c.E.length 1) →
    (passCsOf n c vs r s pp).map (fun x => x.1.E) =
      finE (c :: vs) ((passCsOf n c vs r s pp).map (fun x => x.2.1))
  | 0, c, vs, r, s, pp, hl, hc, _, hcE => by
    have hvs : vs = [] := List.length_eq_zero_iff.1 hl
    subst hvs
    rw [passCsOf_zero]
    simp only [List.map_cons, List.map_nil, finE]
    rw [outRec_Efin c r (by have := hc.1.Elen; omega) (by have := hc.1.O; simpa using this) hcE]
  | n + 1, c, vs, r, s, pp, hl, hc, hvs, hcE => by
    obtain ⟨v0, vs', rfl⟩ : ∃ v0 vs', vs = v0 :: vs' := by
      cases vs with
      | nil => simp at hl
      | cons a b => exact ⟨a, b, rfl⟩
    have hv0 : VI v0 := hvs v0 (by simp)
    have hvs' : ∀ x ∈ vs', VI x := fun x hx => hvs x (by simp [hx])
    have hI1 := (incVisN_val r v0 hv0).1
    have hcg := curG_f _ hI1
    have hl' : ((vs'.map (visN r)).map VR.dec).length = n := by simp at hl ⊢; omega
    have hvs'' : ∀ x ∈ (vs'.map (visN r)).map VR.dec, VI x := by
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := hx
      have := (visIter r z (hvs' z hz)).1
      exact ⟨(visN r z).dec_ok this.1, by
        have := dec_fields' (visN r z); rw [this.2.1]; exact (visIter r z (hvs' z hz)).1.2⟩
    have hk0 := curG_KEq (incVisN r v0) (by have := hI1.1.Elen; omega)
    have IH := passEs n (VR.curG (incVisN r v0)) _ ((incVisN r v0).k - 1) ((incVisN r v0).w - (incVisN r v0).k)
      (outP c r pp) hl' hcg.1 hvs'' (by
        intro h3
        have hO3 : (incVisN r v0).O = 3 := by rw [← hk0.1]; exact h3
        have e1 : (incVisN r v0).curG.E = fld (incVisN r v0).E.length 1 := by simp [VR.curG, VR.cur, hO3, VR.dec]
        have hl1 : 1 ≤ (incVisN r v0).E.length := by have := hI1.1.Elen; omega
        rw [e1, fld_len _ _ hl1])
    rw [passCsOf_succ]
    simp only [List.map_cons, finE]
    refine List.cons_eq_cons.2 ⟨?_, ?_⟩
    · exact outRec_Efin c r (by have := hc.1.Elen; omega) (by have := hc.1.O; simpa using this) hcE
    · rw [IH]
      apply finE_congr
      · simp [hl']
      · intro i a b ha hb
        cases i with
        | zero =>
          simp at ha hb; subst ha; subst hb
          exact KEq_trans hk0 (incVis_KEq r v0 hv0)
        | succ i =>
          simp only [List.getElem?_cons_succ, List.getElem?_map, Option.map_eq_some_iff] at ha hb
          obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := ha
          have hb' : vs'[i]? = some b := by simpa using hb
          have hzb : z = b := Option.some.inj (hz.symm.trans hb')
          subst hzb
          exact decVis_KEq r z (hvs' z (List.mem_of_getElem? hz))



/-- E values after a pass: output records take `val * digit`, the others keep their value. -/
def esN (p : Nat) : List DG → List Nat → List Nat → List Nat
  | g :: gs, e :: es, v :: vl => (if g.2.2.2.2.2 = 2 then e else (v * g.1) % p) :: esN p gs es vl
  | _, _, _ => []

theorem Efin_mkStart (p : Nat) (g : DG) (x e v : Nat) (hp : 2 ≤ p) (hw : g.2.2.2.2.1 = p) (he : e < p) :
    Efin (mkStart g x e) v = fld p ((if g.2.2.2.2.2 = 2 then e else (v * g.1) % p) + 1) := by
  have hl : (mkStart g x e).E.length = p := by
    simp only [mkStart]; rw [fld_len _ _ (by omega), hw]
  unfold Efin
  simp only [mkStart] at hl ⊢
  rw [hw] at hl ⊢
  by_cases hO : g.2.2.2.2.2 = 2
  · simp [hO]
  · simp only [hO, if_false]
    rw [hl]
    have := eAdv_val p (v * g.1) 1 (by omega) (by omega)
    have h2 : eAdv p (v * g.1) 1 = (v * g.1) % p + 1 := by
      have h3 : eAdv p (v * g.1) 1 - 1 = (v * g.1) % p := by simpa using this.2.2
      have h4 := this.1; omega
    rw [h2]

theorem finE_mkSL (p t : Nat) : ∀ (i : Nat) (D : List DG) (es vl : List Nat), 2 ≤ p →
    (∀ g ∈ D, g.2.2.2.2.1 = p) → (∀ e ∈ es, e < p) → D.length = es.length → D.length = vl.length →
    finE (mkSL t i D es) vl = (esN p D es vl).map fun e' => fld p (e' + 1)
  | i, [], [], _, _, _, _, _, _ => by simp [mkSL, finE, esN]
  | i, [], _ :: _, _, _, _, _, h, _ => by simp at h
  | i, _ :: _, [], _, _, _, _, h, _ => by simp at h
  | i, g :: gs, e :: es, [], _, _, _, _, h => by simp at h
  | i, g :: gs, e :: es, v :: vl, hp, hg, he, h1, h2 => by
    simp only [mkSL, finE, esN, List.map_cons]
    rw [Efin_mkStart p g _ e v hp (hg g (by simp)) (he e (by simp))]
    rw [finE_mkSL p t (i + 1) gs es vl hp (fun x hx => hg x (by simp [hx])) (fun x hx => he x (by simp [hx]))
      (by simpa using h1) (by simpa using h2)]


theorem dg_mkStart (g : DG) (x e : Nat) : (mkStart g x e).dg = g := by
  obtain ⟨a, b, c, d, w, o⟩ := g
  simp [VR.dg, mkStart]

theorem mkSL_dg : ∀ (t i : Nat) (D : List DG) (es : List Nat), D.length = es.length →
    (mkSL t i D es).map VR.dg = D
  | t, i, [], [], _ => rfl
  | t, i, [], _ :: _, h => by simp at h
  | t, i, _ :: _, [], h => by simp at h
  | t, i, g :: gs, e :: es, h => by
    simp [mkSL, dg_mkStart, mkSL_dg t (i + 1) gs es (by simpa using h)]

theorem nextPass_mk (R : VR) (x e : Nat) (hm : R.m = 0) (hE : R.E = fld R.dg.2.2.2.2.1 (e + 1)) :
    R.nextPass x = mkStart R.dg x e := by
  simp only [VR.nextPass, mkStart, VR.dg, hE, hm]

theorem nextRecs_eq : ∀ (qs : List VR) (flags : List Nat) (D : List DG) (es' : List Nat) (i0 t' : Nat),
    qs.map VR.dg = D → (∀ q ∈ qs, q.m = 0) → qs.map VR.E = (D.zip es').map (fun q => fld q.1.2.2.2.2.1 (q.2 + 1)) →
    D.length = es'.length →
    flags = (List.range' i0 qs.length).map (fl t') →
    (qs.zip flags).map (fun q => q.1.nextPass q.2) = mkSL t' i0 D es'
  | [], flags, D, es', i0, t', hD, _, _, _, hf => by
    simp at hD; subst hD; simp [mkSL]
  | q :: qs, flags, D, es', i0, t', hD, hm, hE, hl, hf => by
    obtain ⟨g, gs, rfl⟩ : ∃ g gs, D = g :: gs := by
      cases D with
      | nil => simp at hD
      | cons a b => exact ⟨a, b, rfl⟩
    obtain ⟨e, es2, rfl⟩ : ∃ e es2, es' = e :: es2 := by
      cases es' with
      | nil => simp at hl
      | cons a b => exact ⟨a, b, rfl⟩
    simp only [List.map_cons, List.cons.injEq] at hD
    simp only [List.map_cons, List.zip_cons_cons, List.cons.injEq] at hE
    simp only [List.length_cons, List.range'_succ, List.map_cons] at hf
    subst hf
    simp only [List.zip_cons_cons, List.map_cons, mkSL]
    have hq : q.nextPass (fl t' i0) = mkStart g (fl t' i0) e := by
      have := nextPass_mk q (fl t' i0) e (hm q (by simp)) (by rw [hD.1]; exact hE.1)
      rw [this, hD.1]
    rw [hq]
    have ih := nextRecs_eq qs _ gs es2 (i0 + 1) t' hD.2 (fun x hx => hm x (by simp [hx])) hE.2
      (by simpa using hl) rfl
    rw [ih]



theorem passRs (p t N : Nat) (πs ds vals : List Nat) (hp : 0 < p) (hV : ValsOk p t N πs ds vals)
    (n j : Nat) (c : VR) (vs : List VR) (r s : Nat) (pp : Nat × Nat) (hl : vs.length = n) (hN : j + n + 1 = N)
    (hI : ColInv p t j πs ds vals (c :: vs)) (hr : r = c.k - 1) :
    (passCsOf n c vs r s pp).map (fun q => q.2.1) = (List.range (n + 1)).map fun i => vals.getD (j + i) 0 := by
  have h2 := loopRs p t N πs ds vals hp hV n j c vs r s pp hl hN hI hr
  unfold passCsOf
  rw [List.map_append, h2.2.2.1, List.range_succ, List.map_append]
  simp [h2.2.2.2]

theorem esN_length (p : Nat) : ∀ (D : List DG) (es vl : List Nat), D.length = es.length → D.length = vl.length →
    (esN p D es vl).length = D.length
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | g :: gs, e :: es, [], _, h => by simp at h
  | g :: gs, e :: es, v :: vl, h1, h2 => by
    simp [esN, esN_length p gs es vl (by simpa using h1) (by simpa using h2)]

theorem zip_fld (p : Nat) : ∀ (D : List DG) (es' : List Nat), (∀ g ∈ D, g.2.2.2.2.1 = p) →
    (D.zip es').map (fun q => fld q.1.2.2.2.2.1 (q.2 + 1)) = es'.map (fun e => fld p (e + 1)) ∨ D.length ≠ es'.length
  | [], [], _ => Or.inl rfl
  | [], _ :: _, _ => Or.inr (by simp)
  | _ :: _, [], _ => Or.inr (by simp)
  | g :: gs, e :: es, h => by
    rcases zip_fld p gs es (fun x hx => h x (by simp [hx])) with h1 | h1
    · left; simp [h1, h g (by simp)]
    · right; simpa using h1

theorem dec_KEq (v : VR) : KEq (VR.dec v) v := by
  have h1 := dec_EO v
  have h2 := dec_fields' v
  exact ⟨h1.2, h2.1, by rw [h1.1], fun _ => h1.1⟩


theorem curG_k (v : VR) (h : VI v) : v.curG.k = v.k := by
  rw [(curG_f v h).2.2.1]; exact (dec_fields' v).2.2.1

theorem DOk_w {p : Nat} {D : List DG} {es : List Nat} (h : DOk p D es) :
    (∀ g ∈ D, g.2.2.2.2.1 = p) ∧ (∀ e ∈ es, e < p) := by
  obtain ⟨hl, _, h3⟩ := h
  constructor
  · intro g hg
    obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem hg
    have hi' : i < es.length := by omega
    exact (h3 i g es[i] (by rw [List.getElem?_eq_getElem hi, hgi]) (List.getElem?_eq_getElem hi')).1
  · intro e he
    obtain ⟨i, hi, hei⟩ := List.getElem_of_mem he
    have hi' : i < D.length := by omega
    exact (h3 i D[i] e (List.getElem?_eq_getElem hi') (by rw [List.getElem?_eq_getElem hi, hei])).2.2

theorem zip_nextPass : ∀ (xs : List (VR × Nat × Nat)) (fs : List Nat),
    (xs.zip fs).map (fun q => q.1.1.nextPass q.2) = ((xs.map (fun q => q.1)).zip fs).map (fun q => q.1.nextPass q.2)
  | [], _ => rfl
  | x :: xs, [] => rfl
  | x :: xs, f :: fs => by simp [List.zip_cons_cons]; exact zip_nextPass xs fs

theorem passNext (p t : Nat) (D : List DG) (es : List Nat) (hD : DOk p D es) (y0 : VR) (ys : List VR)
    (hy : mkSL t 0 D es = y0 :: ys) (S : Nat) :
    ((passCsOf ys.length y0.curG (ys.map VR.dec) (y0.k - 1) (y0.w - y0.k) (0, S)).zip
        ((List.range' 0 (ys.length + 1)).map (fl (t + 1)))).map (fun q => q.1.1.nextPass q.2) =
      mkSL (t + 1) 0 D (esN p D es ((List.range (ys.length + 1)).map fun i =>
        (valsAux t p 0 (decRecs (D.map fun g => g.2.2.1) (D.map fun g => g.1)) []).getD i 0)) := by
  have hlen := hD.1
  have hp := hD.2.1
  have hL : (y0 :: ys).length = D.length := by rw [← hy]; exact mkSL_length t 0 D es hlen
  have hSR := mkSL_startRec p t D es hD
  rw [hy] at hSR
  have hSR' : ∀ idx y, (y0 :: ys)[idx]? = some y →
      StartRec p (if idx = t then 1 else 0) ((D.map fun g => g.2.2.1).getD idx 0) ((D.map fun g => g.1).getD idx 0) y := hSR
  have hlen2 : (D.map fun g => g.2.2.1).length = (D.map fun g => g.1).length := by simp
  have hV := valsOk_decRecs p t (D.map fun g => g.2.2.1) (D.map fun g => g.1) hlen2
  generalize hvals : valsAux t p 0 (decRecs (D.map fun g => g.2.2.1) (D.map fun g => g.1)) [] = vals at hV ⊢
  have hN : 0 + ys.length + 1 = (D.map fun g => g.2.2.1).length := by rw [List.length_map]; simp only [List.length_cons] at hL; omega
  rw [← hN] at hV
  have hI := startColInv p t _ _ vals (by omega) y0 ys hSR'
  have hVI : ∀ x ∈ y0 :: ys, VI x := fun x hx => by
    obtain ⟨i, hlt, hi⟩ := List.getElem_of_mem hx
    exact (hSR' i x (by rw [List.getElem?_eq_getElem hlt, hi])).1
  have hvy0 : VI y0 := hVI y0 (by simp)
  have hvys : ∀ x ∈ ys, VI x := fun x hx => hVI x (by simp [hx])
  have hr : y0.k - 1 = y0.curG.k - 1 := by rw [curG_k y0 hvy0]
  have hm0 : y0.curG.m = 0 := by rw [(dg_curG y0).2]; exact hvy0.2
  have hvs0 : ∀ x ∈ ys.map VR.dec, x.m = 0 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [(dg_dec z).2]; exact (hvys z hz).2
  have hcl : (passCsOf ys.length y0.curG (ys.map VR.dec) (y0.k - 1) (y0.w - y0.k) (0, S)).length = ys.length + 1 := by
    have := loopRun_cs_length ys.length y0.curG (ys.map VR.dec) (y0.k - 1) (y0.w - y0.k) (0, S) (by simp)
    unfold passCsOf; simp [this]
  rw [zip_nextPass]
  have hqlen : ((passCsOf ys.length y0.curG (ys.map VR.dec) (y0.k - 1) (y0.w - y0.k) (0, S)).map (fun q => q.1)).length = ys.length + 1 := by
    simp [hcl]
  have hesl : (esN p D es ((List.range (ys.length + 1)).map fun i => vals.getD i 0)).length = D.length :=
    esN_length p D es _ hlen (by simp; simp only [List.length_cons] at hL; omega)
  apply nextRecs_eq _ _ D _ 0 (t + 1)
  · have h1 := dg_runAll_pos ys.length y0.curG (ys.map VR.dec) (y0.k - 1) (y0.w - y0.k) (0, S) hm0 hvs0 (by simp)
    rw [List.map_map]
    unfold passCsOf
    have e2 : ((y0.curG :: ys.map VR.dec).map VR.dg) = D := by
      rw [← mkSL_dg t 0 D es hlen, hy]
      simp [dg_curG, List.map_map, Function.comp_def, (dg_dec _).1]
    rw [← e2, ← h1]
    rfl
  · intro q hq
    simp only [List.mem_map] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    have hm := loopRun_m0 ys.length y0.curG (ys.map VR.dec) (y0.k - 1) (y0.w - y0.k) (0, S) hm0 hvs0 (by simp)
    unfold passCsOf at hq'
    simp only [List.mem_append, List.mem_singleton] at hq'
    rcases hq' with h | h
    · exact hm.1 q' h
    · rw [h]; simp only; rw [(outRec_m _ _).1]; exact hm.2
  · have hcE : y0.curG.O = 3 → y0.curG.E = fld y0.curG.E.length 1 := by
      intro h3
      have hk0 := curG_KEq y0 (by have := hvy0.1.Elen; omega)
      have hO3 : y0.O = 3 := by rw [← hk0.1]; exact h3
      have e1 : y0.curG.E = fld y0.E.length 1 := by simp [VR.curG, VR.cur, hO3, VR.dec]
      have hl1 : 1 ≤ y0.E.length := by have := hvy0.1.Elen; omega
      rw [e1, fld_len _ _ hl1]
    have h1 := passEs ys.length y0.curG (ys.map VR.dec) (y0.k - 1) (y0.w - y0.k) (0, S) (by simp)
      (curG_f y0 hvy0).1 (by
        intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨z, hz, rfl⟩ := hx
        exact ⟨z.dec_ok (hvys z hz).1, by rw [(dg_dec z).2]; exact (hvys z hz).2⟩) hcE
    have h2 := passRs p t _ _ _ vals (by omega) hV ys.length 0 y0.curG (ys.map VR.dec) (y0.k - 1) (y0.w - y0.k) (0, S)
      (by simp) rfl hI hr
    rw [List.map_map]
    simp only [Function.comp_def] at h1 ⊢
    rw [h1, h2]
    have hk : finE (y0.curG :: ys.map VR.dec) ((List.range (ys.length + 1)).map fun i => vals.getD (0 + i) 0) =
        finE (y0 :: ys) ((List.range (ys.length + 1)).map fun i => vals.getD (0 + i) 0) := by
      apply finE_congr
      · simp
      · intro i a b ha hb
        cases i with
        | zero => simp at ha hb; subst ha; subst hb; exact curG_KEq y0 (by have := hvy0.1.Elen; omega)
        | succ i =>
          simp only [List.getElem?_cons_succ, List.getElem?_map, Option.map_eq_some_iff] at ha hb
          obtain ⟨z, hz, rfl⟩ := ha
          have hzb : z = b := Option.some.inj (hz.symm.trans hb)
          subst hzb; exact dec_KEq z
    rw [hk, ← hy]
    simp only [Nat.zero_add]
    rw [finE_mkSL p t 0 D es _ hp (DOk_w hD).1 (DOk_w hD).2 hlen (by simp; simp only [List.length_cons] at hL; omega)]
    have hz := zip_fld p D (esN p D es ((List.range (ys.length + 1)).map fun i => vals.getD i 0)) (DOk_w hD).1
    rcases hz with hz | hz
    · exact hz.symm
    · exact absurd hesl.symm hz
  · rw [hesl]
  · rw [hqlen]



theorem fld_cmp (p e v : Nat) (he : e < p) (hv : v < p) :
    (∃ z, 1 ≤ v + 1 ∧ fld p (e + 1) = fld (v + 1 + z) (v + 1)) ↔ e = v := by
  constructor
  · rintro ⟨z, _, h⟩
    have h1 := count3_fld' p (e + 1) (by omega)
    have h2 := count3_fld' (v + 1 + z) (v + 1) (by omega)
    rw [h] at h1; omega
  · rintro rfl
    exact ⟨p - e - 1, by omega, by congr 1; omega⟩

/-- Compare of the `O = 3` records against node values. -/
def CmpD : List DG → List Nat → List Nat → Prop
  | g :: gs, e :: es, v :: vl => (g.2.2.2.2.2 = 3 → e = v) ∧ CmpD gs es vl
  | _, _, _ => True

theorem cmpE_mkSL (p t : Nat) : ∀ (i : Nat) (gs : List DG) (es vl : List Nat),
    (∀ g ∈ gs, g.2.2.2.2.1 = p ∧ (g.2.2.2.2.2 = 2 ∨ g.2.2.2.2.2 = 3)) → (∀ e ∈ es, e < p) → (∀ v ∈ vl, v < p) →
    2 ≤ p → gs.length = es.length →
    (CmpE ((mkSL t i gs es).map VR.dec) vl ↔ CmpD gs es vl)
  | i, [], [], vl, _, _, _, _, _ => by simp [mkSL, CmpE, CmpD]
  | i, [], _ :: _, _, _, _, _, _, h => by simp at h
  | i, _ :: _, [], _, _, _, _, _, h => by simp at h
  | i, g :: gs, e :: es, [], _, _, _, _, _ => by simp [mkSL, CmpE, CmpD]
  | i, g :: gs, e :: es, v :: vl, hg, he, hv, hp, hl => by
    simp only [mkSL, List.map_cons, CmpE, CmpD]
    have hg0 := hg g (by simp)
    have h1 : (mkStart g (fl t i) e).dec.O = g.2.2.2.2.2 := by
      rw [(dec_EO _).2]; rfl
    have h2 : (mkStart g (fl t i) e).dec.E = fld p (e + 1) := by
      rw [(dec_EO _).1]; simp [mkStart, hg0.1]
    rw [h1, h2]
    rw [cmpE_mkSL p t (i + 1) gs es vl (fun x hx => hg x (by simp [hx])) (fun x hx => he x (by simp [hx]))
      (fun x hx => hv x (by simp [hx])) hp (by simpa using hl)]
    have := fld_cmp p e v (he e (by simp)) (hv v (by simp))
    constructor
    · rintro ⟨a, b⟩; exact ⟨fun h => this.1 (a h), b⟩
    · rintro ⟨a, b⟩; exact ⟨fun h => this.2 (a h), b⟩


/-- Node values of pass  for the digit signatures . -/
def valsL (p t : Nat) (D : List DG) : List Nat :=
  (List.range D.length).map fun i =>
    (valsAux t p 0 (decRecs (D.map fun g => g.2.2.1) (D.map fun g => g.1)) []).getD i 0

theorem valsL_lt (p t : Nat) (D : List DG) (hp : 0 < p) : ∀ v ∈ valsL p t D, v < p := by
  intro v hv
  unfold valsL at hv
  simp only [List.mem_map, List.mem_range] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  have hlen2 : (D.map fun g => g.2.2.1).length = (D.map fun g => g.1).length := by simp
  have := valsOk_decRecs p t (D.map fun g => g.2.2.1) (D.map fun g => g.1) hlen2 i (by simpa using hi)
  rw [this]; exact Nat.mod_lt _ hp

theorem valsL_length (p t : Nat) (D : List DG) : (valsL p t D).length = D.length := by simp [valsL]

theorem esN_lt (p : Nat) (hp : 0 < p) : ∀ (D : List DG) (es vl : List Nat), (∀ e ∈ es, e < p) → ∀ x ∈ esN p D es vl, x < p
  | g :: gs, e :: es, v :: vl, he, x, hx => by
    simp only [esN, List.mem_cons] at hx
    rcases hx with rfl | hx
    · split
      · exact he e (by simp)
      · exact Nat.mod_lt _ hp
    · exact esN_lt p hp gs es vl (fun y hy => he y (by simp [hy])) x hx
  | [], _, _, _, x, hx => by simp [esN] at hx
  | _ :: _, [], _, _, x, hx => by simp [esN] at hx
  | _ :: _, _ :: _, [], _, x, hx => by simp [esN] at hx

theorem flags_eq (t N : Nat) (h : t + 2 ≤ N) :
    (List.range' 0 N).map (fl (t + 1)) = List.replicate (t + 1) 2 ++ 3 :: List.replicate (N - t - 2) 2 := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range', fl]
    simp only [List.length_map, List.length_range'] at h1
    by_cases hi : i < t + 1
    · rw [List.getElem_append_left (by simp; omega)]; simp; omega
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_replicate]
      by_cases he : i = t + 1
      · subst he; simp
      · obtain ⟨k, hk⟩ : ∃ k, i - (t + 1) = k + 1 := ⟨i - (t + 1) - 1, by omega⟩
        rw [if_neg (by omega)]
        simp [hk]



theorem DOk_O {p : Nat} {D : List DG} {es : List Nat} (h : DOk p D es) :
    ∀ g ∈ D, g.2.2.2.2.2 = 2 ∨ g.2.2.2.2.2 = 3 := by
  obtain ⟨hl, _, h3⟩ := h
  intro g hg
  obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem hg
  have hi' : i < es.length := by omega
  exact (h3 i g es[i] (by rw [List.getElem?_eq_getElem hi, hgi]) (List.getElem?_eq_getElem hi')).2.1

theorem pass_setup (p t : Nat) (D : List DG) (es : List Nat) (hD : DOk p D es) (y0 : VR) (ys : List VR)
    (hy : mkSL t 0 D es = y0 :: ys) :
    ColInv p t 0 (D.map fun g => g.2.2.1) (D.map fun g => g.1)
      (valsAux t p 0 (decRecs (D.map fun g => g.2.2.1) (D.map fun g => g.1)) []) (y0.curG :: ys.map VR.dec) ∧
    ValsOk p t (ys.length + 1) (D.map fun g => g.2.2.1) (D.map fun g => g.1)
      (valsAux t p 0 (decRecs (D.map fun g => g.2.2.1) (D.map fun g => g.1)) []) ∧
    VI y0 ∧ (∀ x ∈ ys, VI x) ∧ ys.length + 1 = D.length := by
  have hlen := hD.1
  have hp := hD.2.1
  have hL : (y0 :: ys).length = D.length := by rw [← hy]; exact mkSL_length t 0 D es hlen
  have hSR := mkSL_startRec p t D es hD
  rw [hy] at hSR
  have hSR' : ∀ idx y, (y0 :: ys)[idx]? = some y →
      StartRec p (if idx = t then 1 else 0) ((D.map fun g => g.2.2.1).getD idx 0) ((D.map fun g => g.1).getD idx 0) y := hSR
  have hlen2 : (D.map fun g => g.2.2.1).length = (D.map fun g => g.1).length := by simp
  have hV := valsOk_decRecs p t (D.map fun g => g.2.2.1) (D.map fun g => g.1) hlen2
  have hn : ys.length + 1 = D.length := by simpa using hL
  have hN : (D.map fun g => g.2.2.1).length = ys.length + 1 := by rw [List.length_map]; omega
  rw [hN] at hV
  have hI := startColInv p t (D.map fun g => g.2.2.1) (D.map fun g => g.1)
    (valsAux t p 0 (decRecs (D.map fun g => g.2.2.1) (D.map fun g => g.1)) []) (by omega) y0 ys hSR'
  have hVI : ∀ x ∈ y0 :: ys, VI x := fun x hx => by
    obtain ⟨i, hlt, hi⟩ := List.getElem_of_mem hx
    exact (hSR' i x (by rw [List.getElem?_eq_getElem hlt, hi])).1
  exact ⟨hI, hV, hVI y0 (by simp), fun x hx => hVI x (by simp [hx]), hn⟩

theorem pass_cmp (p t : Nat) (D : List DG) (es : List Nat) (hD : DOk p D es) (y0 : VR) (ys : List VR)
    (hy : mkSL t 0 D es = y0 :: ys) :
    PassCmp ys.length (y0.k - 1) (ys.map VR.dec) ↔ CmpD D.tail es.tail (valsL p t D).tail := by
  obtain ⟨hI, hV, hvy0, hvys, hn⟩ := pass_setup p t D es hD y0 ys hy
  have hp := hD.2.1
  have hr : y0.k - 1 = y0.curG.k - 1 := by rw [curG_k y0 hvy0]
  rw [passCmp_iff p t (ys.length + 1) _ _ _ (by omega) hV ys.length 0 y0.curG (ys.map VR.dec) _ (by simp) (by omega) hI hr]
  obtain ⟨g, gs, rfl⟩ : ∃ g gs, D = g :: gs := by
    cases D with
    | nil => simp at hn
    | cons a b => exact ⟨a, b, rfl⟩
  obtain ⟨e, es2, rfl⟩ : ∃ e es2, es = e :: es2 := by
    cases es with
    | nil => have := hD.1; simp at this
    | cons a b => exact ⟨a, b, rfl⟩
  have hys : ys = mkSL t 1 gs es2 := by
    simp only [mkSL] at hy; exact (List.cons.inj hy).2.symm
  have hw := DOk_w hD
  have hvl : (List.range ys.length).map (fun i => (valsAux t p 0 (decRecs ((g :: gs).map fun g => g.2.2.1)
      ((g :: gs).map fun g => g.1)) []).getD (0 + i + 1) 0) = (valsL p t (g :: gs)).tail := by
    unfold valsL
    have : (g :: gs).length = ys.length + 1 := hn.symm
    rw [this, List.range_succ_eq_map]
    simp only [List.map_cons, List.tail_cons, List.map_map]
    apply List.map_congr_left; intro i _; simp only [Function.comp]; congr 1; omega
  rw [hvl, hys]
  have hcl : gs.length = es2.length := by have := hD.1; simpa using this
  have := cmpE_mkSL p t 1 gs es2 (valsL p t (g :: gs)).tail
    (fun x hx => ⟨hw.1 x (by simp [hx]), DOk_O hD x (by simp [hx])⟩) (fun x hx => hw.2 x (by simp [hx])) (fun v hv => valsL_lt p t _ (by omega) v (List.mem_of_mem_tail hv)) hp hcl
  simpa using this


theorem pass_sum (p t : Nat) (D : List DG) (es : List Nat) (hD : DOk p D es) (y0 : VR) (ys : List VR)
    (hy : mkSL t 0 D es = y0 :: ys) (S : Nat) (hS : 1 ≤ S) :
    (passPOf ys.length y0.curG (ys.map VR.dec) (y0.k - 1) (y0.w - y0.k) (0, S)).1 =
      SumOD D (valsL p t D) % S := by
  obtain ⟨hI, hV, hvy0, hvys, hn⟩ := pass_setup p t D es hD y0 ys hy
  have hp := hD.2.1
  have hr : y0.k - 1 = y0.curG.k - 1 := by rw [curG_k y0 hvy0]
  have hm0 : y0.curG.m = 0 := by rw [(dg_curG y0).2]; exact hvy0.2
  have hvs0 : ∀ x ∈ ys.map VR.dec, x.m = 0 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [(dg_dec z).2]; exact (hvys z hz).2
  rw [passPOf_val _ _ _ _ _ _ (by simpa using hS)]
  have := passCs_sum p t (ys.length + 1) _ _ _ (by omega) hV ys.length 0 y0.curG (ys.map VR.dec) (y0.k - 1)
    (y0.w - y0.k) (0, S) (by simp) (by omega) hI hr hm0 hvs0
  rw [this]
  have e2 : ((y0.curG :: ys.map VR.dec).map VR.dg) = D := by
    rw [← mkSL_dg t 0 D es hD.1, hy]
    simp [dg_curG, List.map_map, Function.comp_def, (dg_dec _).1]
  rw [e2]
  have e3 : (List.range (ys.length + 1)).map (fun i => (valsAux t p 0 (decRecs (D.map fun g => g.2.2.1)
      (D.map fun g => g.1)) []).getD (0 + i) 0) = valsL p t D := by
    unfold valsL; rw [← hn]; simp
  rw [e3]
  simp



def H0z (D : List DG) (es : List Nat) : Prop :=
  ∀ g e, D.head? = some g → es.head? = some e → g.2.2.2.2.2 = 3 → e = 0

theorem foks_step (p t m n : Nat) (D : List DG) (es L' : List Nat) (y S : Nat) (hD : DOk p D es) (hS : S = p)
    (hn : D.length = n + 1) (ht : t + 1 ≤ n) (hL : L' = List.replicate (n - t - 1) 2) :
    FOkS (m + 1) n D es t (y :: L') S ↔
      (CmpD D.tail es.tail (valsL p t D).tail ∧ SumOD D (valsL p t D) % S = 0 ∧
        H0z D (esN p D es (valsL p t D)) ∧ FOkS m n D (esN p D es (valsL p t D)) (t + 1) L' S) := by
  have hlen := hD.1
  have hp := hD.2.1
  obtain ⟨g, gs, rfl⟩ : ∃ g gs, D = g :: gs := by
    cases D with
    | nil => simp at hn
    | cons a b => exact ⟨a, b, rfl⟩
  obtain ⟨e, es2, rfl⟩ : ∃ e es2, es = e :: es2 := by
    cases es with
    | nil => simp at hlen
    | cons a b => exact ⟨a, b, rfl⟩
  have hy : mkSL t 0 (g :: gs) (e :: es2) = mkStart g (fl t 0) e :: mkSL t 1 gs es2 := rfl
  generalize hy0 : mkStart g (fl t 0) e = y0 at hy
  generalize hys : mkSL t 1 gs es2 = ys at hy
  have hnys : ys.length = n := by
    have := (pass_setup p t _ _ hD y0 ys hy).2.2.2.2
    simp only [List.length_cons] at this hn; omega
  subst hnys
  have hflag : List.replicate (t + 1) 2 ++ 3 :: L' = (List.range' 0 (ys.length + 1)).map (fl (t + 1)) := by
    rw [flags_eq (t) (ys.length + 1) (by omega), hL]
    congr 3; omega
  have hnext := passNext p t _ _ hD y0 ys hy S
  have hcl : (passCsOf ys.length y0.curG (ys.map VR.dec) (y0.k - 1) (y0.w - y0.k) (0, S)).length = ys.length + 1 := by
    have := loopRun_cs_length ys.length y0.curG (ys.map VR.dec) (y0.k - 1) (y0.w - y0.k) (0, S) (by simp)
    unfold passCsOf; simp [this]
  obtain ⟨t0, ts, hz⟩ : ∃ t0 ts, (passCsOf ys.length y0.curG (ys.map VR.dec) (y0.k - 1) (y0.w - y0.k) (0, S)).zip
      (List.replicate (t + 1) 2 ++ 3 :: L') = t0 :: ts := by
    rw [hflag]
    generalize (passCsOf ys.length y0.curG (ys.map VR.dec) (y0.k - 1) (y0.w - y0.k) (0, S)) = qs at hcl ⊢
    cases qs with
    | nil => simp at hcl
    | cons q qs => exact ⟨_, _, by rw [List.range'_succ, List.map_cons, List.zip_cons_cons]⟩
  have hvl : valsL p t (g :: gs) = (List.range (ys.length + 1)).map fun i =>
      (valsAux t p 0 (decRecs ((g :: gs).map fun g => g.2.2.1) ((g :: gs).map fun g => g.1)) []).getD i 0 := by
    unfold valsL
    have : (g :: gs).length = ys.length + 1 := by simp only [List.length_cons] at hn ⊢; omega
    rw [this]
  rw [← hflag, hz, ← hvl] at hnext
  simp only [List.map_cons] at hnext
  have hnx : mkSL (t + 1) 0 (g :: gs) (esN p (g :: gs) (e :: es2) (valsL p t (g :: gs))) =
      nxtW t0 :: (ts.map fun q => q.1.1.nextPass q.2) := hnext.symm
  have hF : FOkS m ys.length (g :: gs) (esN p (g :: gs) (e :: es2) (valsL p t (g :: gs))) (t + 1) L' S ↔
      FOk m ys.length (nxtC t0) (nxtVs ts) (nxtR t0) (nxtS t0) (0, S) (t + 1) L' := by
    unfold FOkS; rw [hnx]; rfl
  rw [hF]
  have hl0 : FOkS (m + 1) ys.length (g :: gs) (e :: es2) t (y :: L') S ↔
      FOk (m + 1) ys.length y0.curG (ys.map VR.dec) (y0.k - 1) (y0.w - y0.k) (0, S) t (y :: L') := by
    unfold FOkS; rw [hy]
  rw [hl0]
  simp only [FOk, List.tail_cons]
  have hcmp := pass_cmp p t _ _ hD y0 ys hy
  have hsum := pass_sum p t _ _ hD y0 ys hy S (by omega)
  simp only [List.tail_cons] at hcmp
  have hps := passPOf_sum ys.length y0.curG (ys.map VR.dec) (y0.k - 1) (y0.w - y0.k) (0, S) (by simp; omega)
  have hw := DOk_w hD
  -- head of the next pass
  have hv0 : ∃ v0 vl0, valsL p t (g :: gs) = v0 :: vl0 := by
    unfold valsL
    simp only [List.length_cons]
    rw [List.range_succ_eq_map]; simp
  obtain ⟨v0, vl0, hv0⟩ := hv0
  have hhd : nxtW t0 = mkStart g 2 (if g.2.2.2.2.2 = 2 then e else (v0 * g.1) % p) := by
    rw [hv0] at hnx
    simp only [esN, mkSL] at hnx
    have := (List.cons.inj hnx).1.symm
    rw [this]; simp [fl]
  have he0 : (if g.2.2.2.2.2 = 2 then e else (v0 * g.1) % p) < p := by
    split
    · exact hw.2 e (by simp)
    · exact Nat.mod_lt _ (by omega)
  have hcmiff : ((nxtW t0).O = 3 → ∃ z, 1 ≤ (nxtW t0).k ∧ (nxtW t0).E = fld ((nxtW t0).k + z) (nxtW t0).k) ↔
      H0z (g :: gs) (esN p (g :: gs) (e :: es2) (valsL p t (g :: gs))) := by
    rw [hhd, hv0]
    have hfc := fld_cmp p (if g.2.2.2.2.2 = 2 then e else (v0 * g.1) % p) 0 he0 (by omega)
    simp only [mkStart, esN, H0z, List.head?_cons, Option.some.injEq]
    simp only [Nat.zero_add] at hfc
    rw [hw.1 g (by simp)]
    have e2 : (if (2:Nat) = 3 then 2 else 1) = 1 := by decide
    rw [e2]
    generalize (if g.2.2.2.2.2 = 2 then e else (v0 * g.1) % p) = E0 at hfc he0 ⊢
    constructor
    · intro h g' e' hg' he' hO
      subst hg'; subst he'
      obtain ⟨z, h1, h2⟩ := h hO
      exact hfc.1 ⟨z, h1, h2⟩
    · intro h hO
      exact hfc.2 (h g E0 rfl rfl hO)
  have hS0 : (passPOf ys.length y0.curG (ys.map VR.dec) (y0.k - 1) (y0.w - y0.k) (0, S)).1 = 0 ↔
      SumOD (g :: gs) (valsL p t (g :: gs)) % S = 0 := by rw [hsum]
  rw [hcmp]
  constructor
  · rintro ⟨hc, h0, hall⟩
    obtain ⟨hcm, hf⟩ := hall t0 ts hz
    have h2 : (passPOf ys.length y0.curG (ys.map VR.dec) (y0.k - 1) (y0.w - y0.k) (0, S)).2 = S := by
      have := hps.2; rw [h0] at this; simpa using this
    rw [h2] at hf
    exact ⟨hc, hS0.1 h0, hcmiff.1 hcm, hf⟩
  · rintro ⟨hc, hs, h0z, hf⟩
    have h0 := hS0.2 hs
    have h2 : (passPOf ys.length y0.curG (ys.map VR.dec) (y0.k - 1) (y0.w - y0.k) (0, S)).2 = S := by
      have := hps.2; rw [h0] at this; simpa using this
    refine ⟨hc, h0, fun t0' ts' hz' => ?_⟩
    have := hz.symm.trans hz'
    obtain ⟨h1, h3⟩ := List.cons.inj this
    subst h1; subst h3
    rw [h2]
    exact ⟨hcmiff.2 h0z, hf⟩



theorem foks_base (p t n : Nat) (D : List DG) (es : List Nat) (L : List Nat) (S : Nat) (hD : DOk p D es)
    (hS : 1 ≤ S) (hn : D.length = n + 1) :
    FOkS 0 n D es t L S ↔ (CmpD D.tail es.tail (valsL p t D).tail ∧ SumOD D (valsL p t D) % S ≠ 0) := by
  have hlen := hD.1
  obtain ⟨g, gs, rfl⟩ : ∃ g gs, D = g :: gs := by
    cases D with
    | nil => simp at hn
    | cons a b => exact ⟨a, b, rfl⟩
  obtain ⟨e, es2, rfl⟩ : ∃ e es2, es = e :: es2 := by
    cases es with
    | nil => simp at hlen
    | cons a b => exact ⟨a, b, rfl⟩
  have hy : mkSL t 0 (g :: gs) (e :: es2) = mkStart g (fl t 0) e :: mkSL t 1 gs es2 := rfl
  generalize hy0 : mkStart g (fl t 0) e = y0 at hy
  generalize hys : mkSL t 1 gs es2 = ys at hy
  have hnys : ys.length = n := by
    have := (pass_setup p t _ _ hD y0 ys hy).2.2.2.2
    simp only [List.length_cons] at this hn; omega
  subst hnys
  have hl0 : FOkS 0 ys.length (g :: gs) (e :: es2) t L S ↔
      FOk 0 ys.length y0.curG (ys.map VR.dec) (y0.k - 1) (y0.w - y0.k) (0, S) t L := by
    unfold FOkS; rw [hy]
  rw [hl0]
  have hcmp := pass_cmp p t _ _ hD y0 ys hy
  have hsum := pass_sum p t _ _ hD y0 ys hy S hS
  simp only [List.tail_cons] at hcmp
  simp only [FOk, hcmp, hsum]
  rfl



theorem cmpD_iff : ∀ (D : List DG) (es vl : List Nat), D.length = es.length → D.length = vl.length →
    (CmpD D es vl ↔ ∀ (i : Nat) (g : DG), D[i]? = some g → g.2.2.2.2.2 = 3 → es.getD i 0 = vl.getD i 0)
  | [], [], [], _, _ => by simp [CmpD]
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | _ :: _, _ :: _, [], _, h => by simp at h
  | g :: gs, e :: es, v :: vl, h1, h2 => by
    have ih := cmpD_iff gs es vl (by simpa using h1) (by simpa using h2)
    simp only [CmpD, ih]
    constructor
    · rintro ⟨a, b⟩ i g' hg' hO
      cases i with
      | zero => simp at hg'; subst hg'; simpa using a hO
      | succ i => simpa using b i g' (by simpa using hg') hO
    · intro h
      refine ⟨fun hO => by simpa using h 0 g (by simp) hO, fun i g' hg' hO => ?_⟩
      simpa using h (i + 1) g' (by simpa using hg') hO

theorem valsL_head (p t : Nat) (g : DG) (gs : List DG) (hp : 2 ≤ p) :
    (valsL p t (g :: gs)).head? = some (if t = 0 then 1 else 0) := by
  have hlen2 : ((g :: gs).map fun g => g.2.2.1).length = ((g :: gs).map fun g => g.1).length := by simp
  have := valsOk_decRecs p t ((g :: gs).map fun g => g.2.2.1) ((g :: gs).map fun g => g.1) hlen2 0 (by simp)
  unfold valsL
  rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.head?_cons]
  congr 1
  rw [this]
  have hz : ptrVal (ptrOf (((g :: gs).map fun g => g.2.2.1).getD 0 0)) 0 (((g :: gs).map fun g => g.1).getD 0 0)
      (valsAux t p 0 (decRecs ((g :: gs).map fun g => g.2.2.1) ((g :: gs).map fun g => g.1)) []) = 0 := by
    unfold ptrVal; cases ptrOf (((g :: gs).map fun g => g.2.2.1).getD 0 0) <;> simp
  rw [hz]
  by_cases ht : t = 0
  · subst ht; simp; exact Nat.mod_eq_of_lt (by omega)
  · simp [ht, Ne.symm ht]


theorem foldl_add_sum (l : List Nat) : ∀ acc, l.foldl (· + ·) acc = acc + l.sum := by
  induction l with
  | nil => intro acc; simp
  | cons x xs ih => intro acc; simp [ih]; omega

theorem sum_map_mod (p : Nat) (l : List Nat) : (l.map (· % p)).sum % p = l.sum % p := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [List.sum_cons, Nat.add_mod, ih]

theorem sumOD_idx : ∀ (a b : Nat) (D : List DG) (vl : List Nat),
    D.map (fun g => g.2.2.2.2.2) = List.replicate a 2 ++ List.replicate b 3 → D.length = vl.length →
    SumOD D vl = ((List.range b).map fun k => vl.getD (a + k) 0 * (D.map fun g => g.1).getD (a + k) 0).sum
  | a + 1, b, [], vl, h, _ => by simp at h
  | a + 1, b, g :: gs, [], h, hl => by simp at hl
  | a + 1, b, g :: gs, v :: vl, h, hl => by
    simp only [List.map_cons, List.replicate_succ, List.cons_append, List.cons.injEq] at h
    have ih := sumOD_idx a b gs vl h.2 (by simpa using hl)
    simp only [SumOD, h.1, if_true, Nat.zero_add, ih]
    congr 1
    apply List.map_congr_left; intro k _
    rw [Nat.add_right_comm a 1 k]; simp
  | 0, 0, D, vl, h, hl => by
    cases D <;> cases vl <;> simp_all [SumOD]
  | 0, b + 1, [], vl, h, _ => by simp at h
  | 0, b + 1, g :: gs, [], h, hl => by simp at hl
  | 0, b + 1, g :: gs, v :: vl, h, hl => by
    simp only [Nat.zero_add, List.map_cons, List.replicate_zero, List.nil_append, List.replicate_succ,
      List.cons.injEq] at h
    have ih := sumOD_idx 0 b gs vl (by simpa using h.2) (by simpa using hl)
    simp only [SumOD, h.1, show (3 : Nat) ≠ 2 by decide, if_false, Nat.zero_add] at ih ⊢
    rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, ih]
    simp [List.map_map, Function.comp_def, Nat.add_comm 1]



theorem decRecs_snd : ∀ (πs ds : List Nat), πs.length = ds.length → (decRecs πs ds).map Prod.snd = ds
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | π :: πs, d :: ds, h => by simp [decRecs, decRecs_snd πs ds (by simpa using h)]

theorem getD_drop_nat (l : List Nat) (a k : Nat) : (l.drop a).getD k 0 = l.getD (a + k) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem valsL_getD (p t : Nat) (D : List DG) (i : Nat) (hi : i < D.length) :
    (valsL p t D).getD i 0 =
      (valsAux t p 0 (decRecs (D.map fun g => g.2.2.1) (D.map fun g => g.1)) []).getD i 0 := by
  unfold valsL
  simp [List.getD_eq_getElem?_getD, hi]

theorem sum_map_mod2 {α : Type} (p : Nat) (f : α → Nat) : ∀ l : List α,
    ((l.map fun x => f x % p).sum) % p = (l.map f).sum % p
  | [] => by simp
  | x :: xs => by
    simp only [List.map_cons, List.sum_cons]
    rw [Nat.add_mod, sum_map_mod2 p f xs, ← Nat.add_mod]
    rw [Nat.add_mod (f x) _ p]; simp [Nat.mod_mod]

theorem esN_getD (p : Nat) : ∀ (D : List DG) (es vl : List Nat) (i : Nat), D.length = es.length →
    D.length = vl.length → i < D.length →
    (esN p D es vl).getD i 0 =
      (if (D.map fun g => g.2.2.2.2.2).getD i 0 = 2 then es.getD i 0 else (vl.getD i 0 * (D.map fun g => g.1).getD i 0) % p)
  | [], _, _, i, _, _, h => by simp at h
  | g :: gs, [], _, i, h, _, _ => by simp at h
  | g :: gs, e :: es, [], i, _, h, _ => by simp at h
  | g :: gs, e :: es, v :: vl, 0, _, _, _ => by simp [esN]
  | g :: gs, e :: es, v :: vl, i + 1, h1, h2, h3 => by
    simp only [esN, List.getD_cons_succ, List.map_cons]
    exact esN_getD p gs es vl i (by simpa using h1) (by simpa using h2) (by simpa using h3)

theorem HO_get (D : List DG) (a b : Nat) (hHO : D.map (fun g => g.2.2.2.2.2) = List.replicate a 2 ++ List.replicate b 3)
    (k : Nat) (hk : k < b) : ∃ g, D[a + k]? = some g ∧ g.2.2.2.2.2 = 3 := by
  have hl : D.length = a + b := by
    have := congrArg List.length hHO; simpa using this
  have h1 : a + k < D.length := by omega
  refine ⟨D[a + k], List.getElem?_eq_getElem h1, ?_⟩
  have := congrArg (fun l => l[a + k]?) hHO
  simp only [List.getElem?_map, List.getElem?_eq_getElem h1, Option.map_some] at this
  rw [List.getElem?_append_right (by simp)] at this
  simp only [List.length_replicate, Nat.add_sub_cancel_left, List.getElem?_replicate, hk, if_true] at this
  exact Option.some.inj this

theorem HO_lt (D : List DG) (a b : Nat) (hHO : D.map (fun g => g.2.2.2.2.2) = List.replicate a 2 ++ List.replicate b 3)
    (i : Nat) (hi : i < a) (g : DG) (hg : D[i]? = some g) : g.2.2.2.2.2 = 2 := by
  have := congrArg (fun l => l[i]?) hHO
  simp only [List.getElem?_map, hg, Option.map_some] at this
  rw [List.getElem?_append_left (by simpa using hi)] at this
  simp only [List.getElem?_replicate, hi, if_true] at this
  exact Option.some.inj this

open Classical in
/-- One reference pass in digit terms. -/
theorem evalPass_sem (p nr t : Nat) (D : List DG) (es : List Nat) (hD : DOk p D es) (hnr : nr ≤ D.length)
    (hHO : D.map (fun g => g.2.2.2.2.2) = List.replicate (D.length - nr) 2 ++ List.replicate nr 3) :
    evalPass nr p (decRecs (D.map fun g => g.2.2.1) (D.map fun g => g.1)) t (es.drop (D.length - nr)) =
      if CmpD D es (valsL p t D) ∧ (SumOD D (valsL p t D) % p = 0 ↔ t ≠ nr - 1) then
        some ((esN p D es (valsL p t D)).drop (D.length - nr)) else none := by
  have hlen := hD.1
  have hp := hD.2.1
  have hl2 : (D.map fun g => g.2.2.1).length = (D.map fun g => g.1).length := by simp
  have hrl : (decRecs (D.map fun g => g.2.2.1) (D.map fun g => g.1)).length = D.length := by
    rw [decRecs_length _ _ hl2]; simp
  have hsnd := decRecs_snd (D.map fun g => g.2.2.1) (D.map fun g => g.1) hl2
  have hvl : (valsL p t D).length = D.length := valsL_length p t D
  have hcmp := cmpD_iff D es (valsL p t D) hlen hvl.symm
  have hcmpk : CmpD D es (valsL p t D) ↔ ∀ k, k < nr → es.getD (D.length - nr + k) 0 = (valsL p t D).getD (D.length - nr + k) 0 := by
    rw [hcmp]
    constructor
    · intro h k hk
      obtain ⟨g, hg, hO⟩ := HO_get D _ _ hHO k hk
      exact h _ g hg hO
    · intro h i g hg hO
      by_cases hi : i < D.length - nr
      · have := HO_lt D _ _ hHO i hi g hg; omega
      · have hk : i - (D.length - nr) < nr := by
          have : i < D.length := by
            refine Classical.byContradiction fun hc => ?_
            rw [List.getElem?_eq_none (by omega)] at hg; simp at hg
          omega
        have := h (i - (D.length - nr)) hk
        rw [show D.length - nr + (i - (D.length - nr)) = i by omega] at this
        exact this
  unfold evalPass
  simp only [hrl, List.map_drop, hsnd]
  have hall : ((List.range nr).all fun k =>
      (valsAux t p 0 (decRecs (D.map fun g => g.2.2.1) (D.map fun g => g.1)) []).getD (D.length - nr + k) 0 ==
        (es.drop (D.length - nr)).getD k 0) = true ↔
      ∀ k, k < nr → es.getD (D.length - nr + k) 0 = (valsL p t D).getD (D.length - nr + k) 0 := by
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq, getD_drop_nat]
    constructor
    · intro h k hk
      have := h k hk
      rw [valsL_getD p t D _ (by omega)]; exact this.symm
    · intro h k hk
      have := h k hk
      rw [valsL_getD p t D _ (by omega)] at this; exact this.symm
  have hA : CmpD D es (valsL p t D) → ((List.range nr).map fun k =>
      (es.drop (D.length - nr)).getD k 0 * ((D.map fun g => g.1).drop (D.length - nr)).getD k 0 % p) =
      (esN p D es (valsL p t D)).drop (D.length - nr) := by
    intro hC
    have hCk := hcmpk.1 hC
    apply List.ext_getElem?
    intro k
    by_cases hk : k < nr
    · rw [List.getElem?_map, List.getElem?_range hk, List.getElem?_drop]
      have hi : D.length - nr + k < D.length := by omega
      have hel : (esN p D es (valsL p t D)).length = D.length := esN_length p D es _ hlen hvl.symm
      rw [List.getElem?_eq_getElem (by omega : D.length - nr + k < (esN p D es (valsL p t D)).length)]
      simp only [Option.map_some, Option.some.injEq]
      have hg := esN_getD p D es (valsL p t D) (D.length - nr + k) hlen hvl.symm hi
      obtain ⟨g, hgk, hgO⟩ := HO_get D _ _ hHO k hk
      have hO : (D.map fun g => g.2.2.2.2.2).getD (D.length - nr + k) 0 = 3 := by
        simp [List.getD_eq_getElem?_getD, hgk, hgO]
      rw [hO, if_neg (by decide)] at hg
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at hg
      simp only [Option.getD_some] at hg
      rw [hg, getD_drop_nat, getD_drop_nat, hCk k hk]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by
        have hel : (esN p D es (valsL p t D)).length = D.length := esN_length p D es _ hlen hvl.symm
        simp [hel]; omega)]
  have hB : CmpD D es (valsL p t D) → (List.foldl (fun x1 x2 => x1 + x2) 0
      ((esN p D es (valsL p t D)).drop (D.length - nr))) % p = SumOD D (valsL p t D) % p := by
    intro hC
    have hCk := hcmpk.1 hC
    rw [← hA hC, foldl_add_sum, Nat.zero_add,
      sum_map_mod2 p (fun k => (es.drop (D.length - nr)).getD k 0 * ((D.map fun g => g.1).drop (D.length - nr)).getD k 0),
      sumOD_idx _ _ D (valsL p t D) hHO hvl.symm]
    congr 2
    apply List.map_congr_left; intro k hk
    rw [getD_drop_nat, getD_drop_nat, hCk k (List.mem_range.1 hk)]
  split
  · rename_i hall1
    have hC := hcmpk.2 (hall.1 hall1)
    rw [hA hC, hB hC]
    split
    · rename_i hs
      rw [if_neg]
      rintro ⟨_, h2⟩
      generalize SumOD D (valsL p t D) % p = X at hs h2
      cases hxb : (X == 0) <;> cases hyb : (t == nr - 1) <;> simp_all
    · rename_i hs
      have hcnd : CmpD D es (valsL p t D) ∧ (SumOD D (valsL p t D) % p = 0 ↔ t ≠ nr - 1) := by
        refine ⟨hC, ?_⟩
        generalize SumOD D (valsL p t D) % p = X at hs ⊢
        cases hxb : (X == 0) <;> cases hyb : (t == nr - 1) <;> simp_all
      rw [if_pos hcnd]
  · rename_i hall1
    rw [if_neg (fun h => hall1 (hall.2 (hcmpk.1 h.1)))]



def H0 (t : Nat) (D : List DG) (es : List Nat) : Prop :=
  ∀ g e, D.head? = some g → es.head? = some e → g.2.2.2.2.2 = 3 → e = (if t = 0 then 1 else 0)

theorem DOk_esN (p t : Nat) (D : List DG) (es : List Nat) (hD : DOk p D es) :
    DOk p D (esN p D es (valsL p t D)) := by
  have hlen := hD.1
  have hvl := valsL_length p t D
  have hel := esN_length p D es _ hlen hvl.symm
  refine ⟨by rw [hel], hD.2.1, ?_⟩
  intro i g e hg he
  have hi : i < es.length := by
    refine Classical.byContradiction fun hc => ?_
    rw [List.getElem?_eq_none (by omega)] at hg; simp at hg
  have h0 := hD.2.2 i g es[i] hg (List.getElem?_eq_getElem hi)
  refine ⟨h0.1, h0.2.1, ?_⟩
  have hmem : e ∈ esN p D es (valsL p t D) := List.mem_of_getElem? he
  exact esN_lt p (by have := hD.2.1; omega) D es _ (DOk_w hD).2 e hmem

theorem cmp_split (p t : Nat) (D : List DG) (es : List Nat) (hD : DOk p D es) (hne : D ≠ []) :
    CmpD D es (valsL p t D) ↔ (CmpD D.tail es.tail (valsL p t D).tail ∧ H0 t D es) := by
  obtain ⟨g, gs, rfl⟩ : ∃ g gs, D = g :: gs := by
    cases D with
    | nil => exact absurd rfl hne
    | cons a b => exact ⟨a, b, rfl⟩
  obtain ⟨e, es2, rfl⟩ : ∃ e es2, es = e :: es2 := by
    cases es with
    | nil => have := hD.1; simp at this
    | cons a b => exact ⟨a, b, rfl⟩
  have hh := valsL_head p t g gs hD.2.1
  obtain ⟨v0, vl0, hv⟩ : ∃ v0 vl0, valsL p t (g :: gs) = v0 :: vl0 := by
    cases hq : valsL p t (g :: gs) with
    | nil => rw [hq] at hh; simp at hh
    | cons a b => exact ⟨a, b, rfl⟩
  rw [hv] at hh
  simp only [List.head?_cons, Option.some.injEq] at hh
  subst hh
  rw [hv]
  simp only [CmpD, List.tail_cons, H0, List.head?_cons, Option.some.injEq]
  constructor
  · rintro ⟨a, b⟩
    exact ⟨b, fun g' e' hg he hO => by subst hg; subst he; exact a hO⟩
  · rintro ⟨b, a⟩
    exact ⟨fun hO => a g e rfl rfl hO, b⟩


theorem chain (p nr n : Nat) (D : List DG) (hn : D.length = n + 1) (hnrN : nr ≤ n + 1)
    (hHO : D.map (fun g => g.2.2.2.2.2) = List.replicate (n + 1 - nr) 2 ++ List.replicate nr 3) :
    ∀ (m t : Nat) (es L : List Nat), t + m + 1 = nr → DOk p D es → L = List.replicate (n - t) 2 →
      ((H0 t D es ∧ FOkS m n D es t L p) ↔
        (evalFrom nr p (decRecs (D.map fun g => g.2.2.1) (D.map fun g => g.1)) t (m + 1)
          (es.drop (n + 1 - nr))).isSome)
  | 0, t, es, L, ht, hD, hL => by
    have hp := hD.2.1
    have hne : D ≠ [] := by intro h; subst h; simp at hn
    rw [foks_base p t n D es L p hD (by omega) hn]
    have hsem := evalPass_sem p nr t D es hD (by omega) (by rw [hn]; exact hHO)
    rw [hn] at hsem
    simp only [evalFrom]
    rw [hsem]
    have hsplit := cmp_split p t D es hD hne
    have e1 : t = nr - 1 := by omega
    have hcond : (CmpD D es (valsL p t D) ∧ (SumOD D (valsL p t D) % p = 0 ↔ t ≠ nr - 1)) ↔
        (H0 t D es ∧ (CmpD D.tail es.tail (valsL p t D).tail ∧ SumOD D (valsL p t D) % p ≠ 0)) := by
      rw [hsplit]
      have e2 : (t ≠ nr - 1) ↔ False := ⟨fun h => h e1, False.elim⟩
      rw [e2, iff_false]
      constructor
      · rintro ⟨⟨a, c⟩, b⟩; exact ⟨c, a, b⟩
      · rintro ⟨c, a, b⟩; exact ⟨⟨a, c⟩, b⟩
    by_cases hq : CmpD D es (valsL p t D) ∧ (SumOD D (valsL p t D) % p = 0 ↔ t ≠ nr - 1)
    · rw [if_pos hq]; simp only [Option.bind, Option.isSome_some, iff_true]; exact hcond.1 hq
    · rw [if_neg hq]; simp only [Option.bind, Option.isSome_none, Bool.false_eq_true, iff_false]
      exact fun h => hq (hcond.2 h)
  | m + 1, t, es, L, ht, hD, hL => by
    have hp := hD.2.1
    have hne : D ≠ [] := by intro h; subst h; simp at hn
    have htn : t + 1 ≤ n := by omega
    have hL2 : L = 2 :: List.replicate (n - t - 1) 2 := by
      rw [hL, ← List.replicate_succ]; congr 1; omega
    have hstep := foks_step p t m n D es (List.replicate (n - t - 1) 2) 2 p hD rfl hn htn rfl
    rw [hL2, hstep]
    have hsem := evalPass_sem p nr t D es hD (by omega) (by rw [hn]; exact hHO)
    rw [hn] at hsem
    rw [evalFrom, hsem]
    have hsplit := cmp_split p t D es hD hne
    have e1 : t ≠ nr - 1 := by omega
    have hcond : (CmpD D es (valsL p t D) ∧ (SumOD D (valsL p t D) % p = 0 ↔ t ≠ nr - 1)) ↔
        (H0 t D es ∧ (CmpD D.tail es.tail (valsL p t D).tail ∧ SumOD D (valsL p t D) % p = 0)) := by
      rw [hsplit]
      have e2 : (t ≠ nr - 1) ↔ True := ⟨fun _ => trivial, fun _ => e1⟩
      rw [e2, iff_true]
      constructor
      · rintro ⟨⟨a, c⟩, b⟩; exact ⟨c, a, b⟩
      · rintro ⟨c, a, b⟩; exact ⟨⟨a, c⟩, b⟩
    have hH : H0 (t + 1) D (esN p D es (valsL p t D)) ↔ H0z D (esN p D es (valsL p t D)) := by
      simp [H0, H0z]
    have IH := chain p nr n D hn hnrN hHO m (t + 1) (esN p D es (valsL p t D)) (List.replicate (n - t - 1) 2)
      (by omega) (DOk_esN p t D es hD) (by rw [show n - (t + 1) = n - t - 1 by omega])
    by_cases hq : CmpD D es (valsL p t D) ∧ (SumOD D (valsL p t D) % p = 0 ↔ t ≠ nr - 1)
    · rw [if_pos hq]
      obtain ⟨hc0, ha, hb⟩ := hcond.1 hq
      rw [Option.bind_some, ← IH]
      constructor
      · rintro ⟨_, _, _, c, d⟩; exact ⟨hH.2 c, d⟩
      · rintro ⟨c, d⟩; exact ⟨hc0, ha, hb, hH.1 c, d⟩
    · rw [if_neg hq]
      rw [Option.bind_none]; simp only [Option.isSome_none, Bool.false_eq_true, iff_false]
      rintro ⟨c0, a, b, _⟩
      exact hq (hcond.2 ⟨c0, a, b⟩)



theorem AOkD_evalC (p nr n : Nat) (D : List DG) (hp : 2 ≤ p) (hn : D.length = n + 1) (hnr : 1 ≤ nr)
    (hnrN : nr ≤ n + 1)
    (hHO : D.map (fun g => g.2.2.2.2.2) = List.replicate (n + 1 - nr) 2 ++ List.replicate nr 3)
    (hg : ∀ g ∈ D, g.2.2.2.2.1 = p ∧ (g.2.2.2.2.2 = 2 ∨ g.2.2.2.2.2 = 3)) :
    AOkD (nr - 1) n D p ↔
      evalC nr p (decRecs (D.map fun g => g.2.2.1) (D.map fun g => g.1)) = true := by
  rw [AOkD_eq (nr - 1) n D p (fun g h => by have := (hg g h).1; omega)]
  have hDok : DOk p D (List.replicate D.length 1) := by
    refine ⟨by simp, hp, ?_⟩
    intro i g e hgi he
    have hmem : g ∈ D := List.mem_of_getElem? hgi
    have he1 : e = 1 := by
      have := List.mem_of_getElem? he
      exact (by simpa using this : ¬D = [] ∧ e = 1).2
    exact ⟨(hg g hmem).1, (hg g hmem).2, by omega⟩
  have hH0 : H0 0 D (List.replicate D.length 1) := by
    intro g e hgh heh _
    cases D with
    | nil => simp at hgh
    | cons a b =>
      simp only [List.length_cons, List.replicate_succ, List.head?_cons, Option.some.injEq] at heh
      simp [← heh]
  have hc := chain p nr n D hn hnrN hHO (nr - 1) 0 (List.replicate D.length 1) (List.replicate n 2)
    (by omega) hDok (by simp)
  have hl : (List.replicate D.length 1).drop (n + 1 - nr) = List.replicate nr 1 := by
    rw [List.drop_replicate, hn]; congr 1; omega
  rw [hl] at hc
  rw [evalC_eq]
  have : (H0 0 D (List.replicate D.length 1) ∧ FOkS (nr - 1) n D (List.replicate D.length 1) 0 (List.replicate n 2) p) ↔
      FOkS (nr - 1) n D (List.replicate D.length 1) 0 (List.replicate n 2) p :=
    ⟨fun h => h.2, fun h => ⟨hH0, h⟩⟩
  rw [← this, hc]
  have e : nr - 1 + 1 = nr := by omega
  rw [e]



theorem next_dg (o o' : ORec) (ho : o.Ok) (ho' : o'.Ok) (h : o.dgO = o'.dgO) :
    (∀ a, o.next = Sum.inl a → ∃ a', o'.next = Sum.inl a' ∧ a.dgO = a'.dgO) ∧
    (∀ a, o.next = Sum.inr a → ∃ a', o'.next = Sum.inr a' ∧ a.dgO = a'.dgO) := by
  have d1 := ho.d
  have d2 := ho'.d
  have k1 := ho.k
  have k2 := ho'.k
  simp only [ORec.dgO, Prod.mk.injEq] at h
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h
  have hr : o.r = o'.r := by omega
  constructor
  · intro a ha
    unfold ORec.next at ha
    by_cases c1 : o.d + 1 < o.r
    · rw [if_pos c1] at ha
      cases ha
      refine ⟨{ o' with d := o'.d + 1 }, ?_, ?_⟩
      · unfold ORec.next; rw [if_pos (by omega)]
      · simp only [ORec.dgO]; simp only [Prod.mk.injEq]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | omega | trivial
    · rw [if_neg c1] at ha
      by_cases c2 : 1 ≤ o.m
      · rw [if_pos c2] at ha
        cases ha
        refine ⟨{ o' with d := 0, k := o'.k + 1, m := o'.m - 1 }, ?_, ?_⟩
        · unfold ORec.next; rw [if_neg (by omega), if_pos (by omega)]
        · simp only [ORec.dgO]; simp only [Prod.mk.injEq]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | omega | trivial
      · rw [if_neg c2] at ha
        cases ha
  · intro a ha
    unfold ORec.next at ha
    by_cases c1 : o.d + 1 < o.r
    · rw [if_pos c1] at ha; cases ha
    · rw [if_neg c1] at ha
      by_cases c2 : 1 ≤ o.m
      · rw [if_pos c2] at ha; cases ha
      · rw [if_neg c2] at ha
        cases ha
        refine ⟨{ o' with d := 0, z := 0, k := 1, m := o'.z + o'.k - 1 }, ?_, ?_⟩
        · unfold ORec.next; rw [if_neg (by omega), if_neg (by omega)]
        · simp only [ORec.dgO]; simp only [Prod.mk.injEq]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | omega | trivial

theorem odo_dg : ∀ (es es' : List ORec), (∀ x ∈ es, x.Ok) → (∀ x ∈ es', x.Ok) →
    es.map ORec.dgO = es'.map ORec.dgO →
    (∀ t, odoStepR es = some t → ∃ t', odoStepR es' = some t' ∧ t.map ORec.dgO = t'.map ORec.dgO) ∧
    (odoStepR es = none → odoStepR es' = none)
  | [], [], _, _, _ => ⟨by simp [odoStepR], fun _ => rfl⟩
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | o :: os, o' :: os', h1, h2, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hh, ht⟩ := h
    have ih := odo_dg os os' (fun x hx => h1 x (by simp [hx])) (fun x hx => h2 x (by simp [hx])) ht
    have nd := next_dg o o' (h1 o (by simp)) (h2 o' (by simp)) hh
    constructor
    · intro t hT
      unfold odoStepR at hT
      cases hn : o.next with
      | inl a =>
        rw [hn] at hT
        cases hT
        obtain ⟨a', ha', hd⟩ := nd.1 a hn
        refine ⟨a' :: os', ?_, by simp [hd, ht]⟩
        unfold odoStepR; rw [ha']
      | inr a =>
        rw [hn] at hT
        simp only [Option.map_eq_some_iff] at hT
        obtain ⟨u, hu, rfl⟩ := hT
        obtain ⟨u', hu', hd⟩ := ih.1 u hu
        obtain ⟨a', ha', hd2⟩ := nd.2 a hn
        refine ⟨a' :: u', ?_, by simp [hd, hd2]⟩
        unfold odoStepR; rw [ha']; simp [hu']
    · intro hN
      unfold odoStepR at hN ⊢
      cases hn : o.next with
      | inl a => rw [hn] at hN; cases hN
      | inr a =>
        rw [hn] at hN
        obtain ⟨a', ha', _⟩ := nd.2 a hn
        rw [ha']
        have : odoStepR os = none := by
          cases hh : odoStepR os with
          | none => rfl
          | some u => rw [hh] at hN; simp at hN
        simp [ih.2 this]

theorem rt_ph {a b : List ORec} (h : Rt OS a b) (ha : ∀ x ∈ a, x.Ok) :
    (∀ x ∈ b, x.Ok) ∧ (b = a ∨ ph (b.map ORec.dgO) < ph (a.map ORec.dgO)) := by
  induction h with
  | refl => exact ⟨ha, Or.inl rfl⟩
  | @tail b0 c0 _ hs ih =>
    obtain ⟨hb, hb2⟩ := ih
    obtain ⟨o2, os2, rfl, _, hok2, _⟩ := odo_ok b0 c0 hb hs
    refine ⟨hok2, Or.inr ?_⟩
    have := odo_dec b0 _ hb hs
    rcases hb2 with rfl | h2
    · exact this
    · exact Nat.lt_trans this h2

theorem rt_antisymm {a b : List ORec} (ha : ∀ x ∈ a, x.Ok) (h1 : Rt OS a b) (h2 : Rt OS b a) : b = a := by
  obtain ⟨hb, h1'⟩ := rt_ph h1 ha
  obtain ⟨_, h2'⟩ := rt_ph h2 hb
  rcases h1' with h | h1'
  · exact h
  · rcases h2' with h | h2'
    · exact h.symm
    · exact absurd (Nat.lt_trans h1' h2') (Nat.lt_irrefl _)

theorem diters_lift (m n s : Nat) {D D3 : List DG} (h : DIterS m n s D D3) :
    ∀ es : List ORec, (∀ x ∈ es, x.Ok) → es.map ORec.dgO = D →
    ∃ es3 : List ORec, (∀ x ∈ es3, x.Ok) ∧ es3.map ORec.dgO = D3 ∧ Rt OS es es3 ∧
      ∀ e', Rt OS es e' → Rt OS e' es3 → e' = es3 ∨ ¬ AOkD m n (e'.map ORec.dgO) s := by
  induction h with
  | refl D =>
    intro es hok hd
    exact ⟨es, hok, hd, Rt.refl _, fun e' h1 h2 => Or.inl (rt_antisymm hok h1 h2)⟩
  | step hs hn _ ih =>
    rename_i D D2 D3
    intro es hok hd
    obtain ⟨o, os, o2, os2, hO, hD, hS, hD2⟩ := hs
    have hdg := odo_dg (o :: os) es hO hok (by rw [hd, hD])
    obtain ⟨t', ht', htd⟩ := hdg.1 _ hS
    obtain ⟨a, as, rfl, _, hok2, _⟩ := odo_ok es t' hok ht'
    obtain ⟨es3, hok3, hd3, hr3, hp⟩ := ih (a :: as) hok2 (by rw [← hD2, htd])
    have hOS : OS es (a :: as) := ht'
    refine ⟨es3, hok3, hd3, (Rt.tail (Rt.refl _) hOS).trans hr3, fun e' h1 h2 => ?_⟩
    rcases Rt.det_step OS_det hOS h1 with rfl | h1'
    · exact Or.inr (by rw [hd]; exact hn)
    · exact hp e' h1' h2

/-- Odometer link: a terminating refuted iteration refutes every in-range digit assignment. -/
theorem diters_refute (m n s : Nat) (os : List ORec) (hok : ∀ x ∈ os, x.Ok)
    (hI : ∀ x ∈ os, x.z = 0 ∧ x.k = 1 ∧ x.d = 0 ∧ 1 ≤ x.r) {D : List DG}
    (hit : DIterS m n s (os.map ORec.dgO) D) (hterm : StepNone D) (hno : ¬ AOkD m n D s)
    (πs ds : List Nat) (hF : Fit os πs ds) : ¬ AOkD m n ((setD os πs ds).map ORec.dgO) s := by
  obtain ⟨es3, hok3, hd3, hr3, hp⟩ := diters_lift m n s hit os hok rfl
  obtain ⟨o, os', ho, hdo, hn⟩ := hterm
  have hdg := odo_dg (o :: os') es3 ho hok3 (by rw [hdo, hd3])
  have hn3 : odoStepR es3 = none := hdg.2 hn
  obtain ⟨hv1, hv2⟩ := odo_all_visited os es3 hI hr3 hn3 πs ds hF
  rcases hp _ hv2 hv1 with h | h
  · rw [h, hd3]; exact hno
  · exact h



/-- `x` is the record of `y` at some digits `(π, d)` in range. -/
def AtF (y x : ORec) : Prop := ∃ π d, π ≤ y.m ∧ d < y.r ∧ x = y.at π d

theorem next_at (y x : ORec) (h0 : y.z = 0) (h1 : y.k = 1) (hx : AtF y x) :
    (∀ x', x.next = Sum.inl x' → AtF y x') ∧ (∀ x', x.next = Sum.inr x' → AtF y x') := by
  obtain ⟨π, d, hπ, hd, rfl⟩ := hx
  have key : ∀ π d, (y.at π d).z = 0 ∧ (y.at π d).k = π + 1 ∧ (y.at π d).d = d ∧ (y.at π d).r = y.r ∧
      (y.at π d).m = y.m - π := by
    intro π d; simp [ORec.at, h0, h1]
  obtain ⟨k0, k1, k2, k3, k4⟩ := key π d
  constructor
  · intro x' hx'
    unfold ORec.next at hx'
    rw [k2, k3] at hx'
    by_cases c1 : d + 1 < y.r
    · rw [if_pos c1] at hx'; cases hx'
      exact ⟨π, d + 1, hπ, c1, by simp [ORec.at]⟩
    · rw [if_neg c1] at hx'
      by_cases c2 : 1 ≤ (y.at π d).m
      · rw [if_pos c2] at hx'; cases hx'
        refine ⟨π + 1, 0, by omega, by omega, ?_⟩
        simp [ORec.at, h0, h1]; omega
      · rw [if_neg c2] at hx'; cases hx'
  · intro x' hx'
    unfold ORec.next at hx'
    rw [k2, k3] at hx'
    by_cases c1 : d + 1 < y.r
    · rw [if_pos c1] at hx'; cases hx'
    · rw [if_neg c1] at hx'
      by_cases c2 : 1 ≤ (y.at π d).m
      · rw [if_pos c2] at hx'; cases hx'
      · rw [if_neg c2] at hx'; cases hx'
        refine ⟨0, 0, by omega, by omega, ?_⟩
        simp [ORec.at, h0, h1]
        omega

/-- Pointwise `AtF` against the initial list. -/
def AtL : List ORec → List ORec → Prop
  | [], [] => True
  | y :: ys, x :: xs => AtF y x ∧ AtL ys xs
  | _, _ => False

theorem odo_atL : ∀ (os es es' : List ORec), (∀ x ∈ os, x.z = 0 ∧ x.k = 1) → AtL os es →
    odoStepR es = some es' → AtL os es'
  | [], [], _, _, _, h => by simp [odoStepR] at h
  | [], _ :: _, _, _, h, _ => by simp [AtL] at h
  | _ :: _, [], _, _, h, _ => by simp [AtL] at h
  | y :: ys, e :: es, es', hI, hA, h => by
    obtain ⟨hy, hys⟩ := hA
    obtain ⟨a0, a1⟩ := hI y (by simp)
    have nx := next_at y e a0 a1 hy
    unfold odoStepR at h
    cases hn : e.next with
    | inl a =>
      rw [hn] at h; cases h
      exact ⟨nx.1 a hn, hys⟩
    | inr a =>
      rw [hn] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨u, hu, rfl⟩ := h
      exact ⟨nx.2 a hn, odo_atL ys es u (fun x hx => hI x (by simp [hx])) hys hu⟩

theorem atL_refl : ∀ (os : List ORec), (∀ x ∈ os, 1 ≤ x.r) → (∀ x ∈ os, x.d = 0 ∧ x.z = 0 ∧ x.k = 1) → AtL os os
  | [], _, _ => trivial
  | y :: ys, h1, h2 => by
    refine ⟨⟨0, 0, by omega, h1 y (by simp), ?_⟩, atL_refl ys (fun x hx => h1 x (by simp [hx])) (fun x hx => h2 x (by simp [hx]))⟩
    obtain ⟨a, b, c⟩ := h2 y (by simp)
    cases y; simp_all [ORec.at]

theorem rt_atL (os : List ORec) (hI : ∀ x ∈ os, x.z = 0 ∧ x.k = 1) {e : List ORec} (h : Rt OS os e) (h0 : AtL os os) : AtL os e := by
  induction h with
  | refl => exact h0
  | tail _ hs ih => exact odo_atL os _ _ hI ih hs

theorem atL_setD : ∀ (os es : List ORec), AtL os es → ∃ πs ds, Fit os πs ds ∧ es = setD os πs ds
  | [], [], _ => ⟨[], [], trivial, rfl⟩
  | [], _ :: _, h => by simp [AtL] at h
  | _ :: _, [], h => by simp [AtL] at h
  | y :: ys, e :: es, h => by
    obtain ⟨⟨π, d, h1, h2, rfl⟩, h3⟩ := h
    obtain ⟨πs, ds, hF, rfl⟩ := atL_setD ys es h3
    exact ⟨π :: πs, d :: ds, ⟨h1, h2, hF⟩, rfl⟩

theorem setD_map (f : ORec → Nat) (hf : ∀ o π d, f (o.at π d) = f o) :
    ∀ (os : List ORec) (πs ds : List Nat), Fit os πs ds → (setD os πs ds).map f = os.map f
  | [], πs, ds, h => by cases πs <;> cases ds <;> first | rfl | (simp [Fit] at h)
  | _ :: _, [], _, h => by simp [Fit] at h
  | _ :: _, _ :: _, [], h => by simp [Fit] at h
  | o :: os, π :: πs, d :: ds, h => by
    simp only [setD, List.map_cons, hf]
    rw [setD_map f hf os πs ds h.2.2]

theorem setD_pi : ∀ (os : List ORec) (πs ds : List Nat), Fit os πs ds →
    ((setD os πs ds).map ORec.dgO).map (fun g => g.2.2.1) = πs ∧
    ((setD os πs ds).map ORec.dgO).map (fun g => g.1) = ds
  | [], πs, ds, h => by cases πs <;> cases ds <;> first | exact ⟨rfl, rfl⟩ | (simp [Fit] at h)
  | _ :: _, [], _, h => by simp [Fit] at h
  | _ :: _, _ :: _, [], h => by simp [Fit] at h
  | o :: os, π :: πs, d :: ds, h => by
    have ih := setD_pi os πs ds h.2.2
    simp only [setD, List.map_cons, ORec.dgO, ORec.at]
    refine ⟨?_, ?_⟩
    · rw [ih.1]; simp
    · rw [ih.2]

/-- Initial records of the width-`p` circuit variables, numbered from `i`. -/
def initFrom (p : Nat) : Nat → List Nat → List ORec
  | _, [] => []
  | i, O :: Os => recO (p - 1) (O, i + 1) :: initFrom p (i + 1) Os

theorem initFrom_len (p : Nat) : ∀ i Os, (initFrom p i Os).length = Os.length
  | _, [] => rfl
  | i, _ :: Os => by simp [initFrom, initFrom_len p (i + 1) Os]

theorem initFrom_I (p : Nat) (hp : 1 ≤ p) : ∀ i Os, ∀ x ∈ initFrom p i Os, x.z = 0 ∧ x.k = 1 ∧ x.d = 0 ∧ 1 ≤ x.r
  | _, [] => by simp [initFrom]
  | i, O :: Os => by
    intro x hx
    simp only [initFrom, List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp [recO] <;> omega
    · exact initFrom_I p hp (i + 1) Os x hx

theorem initFrom_Ok (p : Nat) (hp : 2 ≤ p) : ∀ i Os, (∀ O ∈ Os, O = 2 ∨ O = 3) → ∀ x ∈ initFrom p i Os, x.Ok
  | _, [], _ => by simp [initFrom]
  | i, O :: Os, hO => by
    intro x hx
    simp only [initFrom, List.mem_cons] at hx
    rcases hx with rfl | hx
    · have hO0 := hO O (by simp)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [recO] <;> omega
      · intro y hy; simp [recO, List.mem_replicate] at hy; rcases hy with rfl | ⟨_, rfl⟩ <;> simp
      · intro y hy; simp [recO, List.mem_replicate] at hy; rcases hy with rfl | ⟨_, rfl⟩ <;> simp
      · simp [recO] <;> omega
      · simp [recO]
      · simp [recO] <;> omega
      · simp [recO]
    · exact initFrom_Ok p hp (i + 1) Os (fun O h => hO O (by simp [h])) x hx

theorem initFrom_fit (p : Nat) (hp : 1 ≤ p) : ∀ i Os πs ds, Fit (initFrom p i Os) πs ds ↔ DigOk p i πs ds ∧ πs.length = Os.length
  | i, [], πs, ds => by
    cases πs <;> cases ds <;> simp [initFrom, Fit, DigOk]
  | i, O :: Os, πs, ds => by
    cases πs with
    | nil => cases ds <;> simp [initFrom, Fit, DigOk]
    | cons π πs =>
      cases ds with
      | nil => simp [initFrom, Fit, DigOk]
      | cons d ds =>
        have ih := initFrom_fit p hp (i + 1) Os πs ds
        simp only [initFrom, Fit, DigOk, recO, List.length_cons, ih]
        constructor
        · rintro ⟨a, b, c, d'⟩; exact ⟨⟨a, by omega, c⟩, by omega⟩
        · rintro ⟨⟨a, b, c⟩, d'⟩; exact ⟨a, by omega, c, by omega⟩

theorem initFrom_mem (p : Nat) (hp : 1 ≤ p) : ∀ i Os, ∀ x ∈ initFrom p i Os, x.acc.length = p ∧ x.O ∈ Os
  | _, [] => by simp [initFrom]
  | i, O :: Os => by
    intro x hx
    simp only [initFrom, List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp [recO]; omega
    · have := initFrom_mem p hp (i + 1) Os x hx
      exact ⟨this.1, by simp [this.2]⟩

theorem initFrom_O (p : Nat) : ∀ i Os, (initFrom p i Os).map ORec.O = Os
  | _, [] => rfl
  | i, O :: Os => by simp [initFrom, recO, initFrom_O p (i + 1) Os]

theorem atL_len : ∀ (os es : List ORec), AtL os es → es.length = os.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [AtL] at h
  | _ :: _, [], h => by simp [AtL] at h
  | y :: ys, e :: es, h => by simp [atL_len ys es h.2]

theorem setD_len : ∀ (os : List ORec) (πs ds : List Nat), Fit os πs ds → (setD os πs ds).length = os.length
  | [], πs, ds, h => by cases πs <;> cases ds <;> first | rfl | (simp [Fit] at h)
  | _ :: _, [], _, h => by simp [Fit] at h
  | _ :: _, _ :: _, [], h => by simp [Fit] at h
  | o :: os, π :: πs, d :: ds, h => by simp [setD, setD_len os πs ds h.2.2]

theorem setD_spec (p nr n : Nat) (Os : List Nat) (hp : 2 ≤ p) (hnr : 1 ≤ nr) (hnrN : nr ≤ n + 1)
    (hOl : Os.length = n + 1) (hOs : Os = List.replicate (n + 1 - nr) 2 ++ List.replicate nr 3)
    (πs ds : List Nat) (hF : Fit (initFrom p 0 Os) πs ds) :
    AOkD (nr - 1) n ((setD (initFrom p 0 Os) πs ds).map ORec.dgO) p ↔ evalC nr p (decRecs πs ds) = true := by
  have hO23 : ∀ O ∈ Os, O = 2 ∨ O = 3 := by
    intro O hO; rw [hOs] at hO; simp [List.mem_replicate] at hO; omega
  have hlen := setD_len _ _ _ hF
  have e1 := setD_map (fun x => x.acc.length) (fun o π d => by simp [ORec.at]) _ _ _ hF
  have e2 := setD_map ORec.O (fun o π d => by simp [ORec.at]) _ _ _ hF
  have hpd := setD_pi _ _ _ hF
  have key := AOkD_evalC p nr n ((setD (initFrom p 0 Os) πs ds).map ORec.dgO) hp
    (by simp [hlen, initFrom_len, hOl]) hnr hnrN
  rw [hpd.1, hpd.2] at key
  apply key
  · rw [List.map_map]
    have : ((fun g : DG => g.2.2.2.2.2) ∘ ORec.dgO) = ORec.O := by funext x; simp [ORec.dgO]
    rw [this, e2, initFrom_O, hOs]
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    have h1 : x.acc.length ∈ (initFrom p 0 Os).map (fun x => x.acc.length) := by
      rw [← e1]; exact List.mem_map.2 ⟨x, hx, rfl⟩
    have h2 : x.O ∈ (initFrom p 0 Os).map ORec.O := by
      rw [← e2]; exact List.mem_map.2 ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hy2⟩ := List.mem_map.1 h1
    rw [initFrom_O] at h2
    refine ⟨?_, hO23 _ h2⟩
    simp only [ORec.dgO]
    rw [← hy2]; exact (initFrom_mem p (by omega) 0 Os y hy).1

/-- Failure of the loop refutes every digit assignment. -/
theorem loop_none (p nr n : Nat) (Os : List Nat) (hp : 2 ≤ p) (hnr : 1 ≤ nr) (hnrN : nr ≤ n + 1)
    (hOl : Os.length = n + 1) (hOs : Os = List.replicate (n + 1 - nr) 2 ++ List.replicate nr 3)
    {D : List DG} (hit : DIterS (nr - 1) n p ((initFrom p 0 Os).map ORec.dgO) D)
    (hterm : StepNone D) (hno : ¬ AOkD (nr - 1) n D p) :
    ¬ ∃ πs ds, DigOk p 0 πs ds ∧ πs.length = n + 1 ∧ evalC nr p (decRecs πs ds) = true := by
  have hO23 : ∀ O ∈ Os, O = 2 ∨ O = 3 := by
    intro O hO; rw [hOs] at hO; simp [List.mem_replicate] at hO; omega
  rintro ⟨πs, ds, h1, h2, h3⟩
  have hF : Fit (initFrom p 0 Os) πs ds := (initFrom_fit p (by omega) 0 Os πs ds).2 ⟨h1, by omega⟩
  exact diters_refute (nr - 1) n p _ (initFrom_Ok p hp 0 Os hO23) (initFrom_I p (by omega) 0 Os) hit hterm hno
    πs ds hF ((setD_spec p nr n Os hp hnr hnrN hOl hOs πs ds hF).2 h3)

/-- Success of the loop yields a circuit assignment. -/
theorem loop_some (p nr n : Nat) (Os : List Nat) (hp : 2 ≤ p) (hnr : 1 ≤ nr) (hnrN : nr ≤ n + 1)
    (hOl : Os.length = n + 1) (hOs : Os = List.replicate (n + 1 - nr) 2 ++ List.replicate nr 3)
    {D : List DG} (hit : DIterS (nr - 1) n p ((initFrom p 0 Os).map ORec.dgO) D)
    (hs : AOkD (nr - 1) n D p) :
    ∃ πs ds, DigOk p 0 πs ds ∧ πs.length = n + 1 ∧ evalC nr p (decRecs πs ds) = true := by
  have hO23 : ∀ O ∈ Os, O = 2 ∨ O = 3 := by
    intro O hO; rw [hOs] at hO; simp [List.mem_replicate] at hO; omega
  obtain ⟨es3, hok3, hd3, hr3, _⟩ := diters_lift (nr - 1) n p hit _ (initFrom_Ok p hp 0 Os hO23) rfl
  have hI := initFrom_I p (by omega) 0 Os
  have hA := rt_atL _ (fun x hx => ⟨(hI x hx).1, (hI x hx).2.1⟩) hr3
    (atL_refl _ (fun x hx => (hI x hx).2.2.2) (fun x hx => ⟨(hI x hx).2.2.1, (hI x hx).1, (hI x hx).2.1⟩))
  obtain ⟨πs, ds, hF, rfl⟩ := atL_setD _ _ hA
  subst hd3
  refine ⟨πs, ds, ((initFrom_fit p (by omega) 0 Os πs ds).1 hF).1, ?_, (setD_spec p nr n Os hp hnr hnrN hOl hOs πs ds hF).1 hs⟩
  have := ((initFrom_fit p (by omega) 0 Os πs ds).1 hF).2
  omega



/-- Loop outcome gives the circuit verdict together with the machine continuation. -/
theorem lp_circuit (pr : Nat → Nat) (c nr n p : Nat) (Os : List Nat) (hpr : pr nr = p) (hcn : c * nr = n + 1)
    (hp : 2 ≤ p) (hnr : 1 ≤ nr) (hnrN : nr ≤ n + 1)
    (hOl : Os.length = n + 1) (hOs : Os = List.replicate (n + 1 - nr) 2 ++ List.replicate nr 3)
    (Wf Kf Cf : List Nat) (st : ZC) {D : List DG}
    (hit : DIterS (nr - 1) n p ((initFrom p 0 Os).map ORec.dgO) D)
    (hl : LpOut Wf Kf Cf (nr - 1) n st D p) :
    (hasCircuit pr c nr = false ∧ ∃ (A : List Nat) (n0 : Nat), znttLogic.Reach st (hd QNTT.BEEP A []) ∧
      ∃ X, znttLogic.zstep (hd QNTT.BEEP A []) = some X ∧
        znttLogic.Reach X (hdR QNTT.PA0 [3] (1 :: (Kf.map (fun x => if x = 1 then 1 else 3) ++ 1 ::
          ((Cf.map (fun x => if x = 1 then 1 else 3) ++ [3]) ++ 1 ::
            (List.replicate (nr - 1 + 1 + 0) 3 ++ List.replicate (n0 + 1) 0)))))) ∨
    (hasCircuit pr c nr = true ∧ ∃ N : Nat, ∃ T, SuOut D Wf (Kf ++ 1 :: Cf) (0 + (nr - 1) + 1) T ∧
      znttLogic.Reach st (hdR QNTT.SU1 [] T) ∧
      znttLogic.Reach (hdR QNTT.SU1 [] T) (hdR QNTT.PA0 [3] (1 :: (Kf ++ 1 :: (Cf ++ 1 :: (List.replicate (0 + (nr - 1) + 1 + 1) 3 ++
        List.replicate (N + 1) 0)))))) := by
  have hiff := hasCircuit_iff pr c nr
  rw [hpr, hcn] at hiff
  rcases hl with ⟨A, n0, hT, hno, hr, X, hX, hr2⟩ | ⟨N, T, hs, hf, h1, h3⟩
  · left
    refine ⟨?_, A, n0, hr, X, hX, hr2⟩
    cases hh : hasCircuit pr c nr with
    | false => rfl
    | true =>
      exact absurd (hiff.1 hh) (loop_none p nr n Os hp hnr hnrN hOl hOs hit hT hno)
  · right
    refine ⟨?_, N, T, hs, h1, h3⟩
    exact hiff.2 (loop_some p nr n Os hp hnr hnrN hOl hOs hit hf)

theorem initFrom_cons (p n : Nat) (Os : List Nat) (hOl : Os.length = n + 1) :
    ∃ o os, initFrom p 0 Os = o :: os ∧ os.length = n := by
  cases Os with
  | nil => simp at hOl
  | cons O Os' => exact ⟨_, _, rfl, by simpa [initFrom_len] using hOl⟩

/-- The assignment loop started at the canonical initial records decides `hasCircuit`. -/
theorem assign_circuit (pr : Nat → Nat) (c nr n p : Nat) (Os : List Nat) (hpr : pr nr = p) (hcn : c * nr = n + 1)
    (hp : 2 ≤ p) (hnr : 1 ≤ nr) (hnrN : nr ≤ n + 1)
    (hOl : Os.length = n + 1) (hOs : Os = List.replicate (n + 1 - nr) 2 ++ List.replicate nr 3)
    (a k c' : Nat) (hk : 1 ≤ k) (hc' : 1 ≤ c') (o : ORec) (os : List ORec) (ho : initFrom p 0 Os = o :: os)
    (hlen : os.length = n) :
    (hasCircuit pr c nr = false ∧ ∃ (A : List Nat) (n0 : Nat),
      znttLogic.Reach (loopSt (List.replicate a 3) (List.replicate k 3) (List.replicate c' 3) (nr - 1) p o os)
        (hd QNTT.BEEP A []) ∧
      ∃ X, znttLogic.zstep (hd QNTT.BEEP A []) = some X ∧
        znttLogic.Reach X (hdR QNTT.PA0 [3] (1 :: ((List.replicate k 3).map (fun x => if x = 1 then 1 else 3) ++ 1 ::
          (((List.replicate c' 3).map (fun x => if x = 1 then 1 else 3) ++ [3]) ++ 1 ::
            (List.replicate (nr - 1 + 1 + 0) 3 ++ List.replicate (n0 + 1) 0)))))) ∨
    (hasCircuit pr c nr = true ∧ ∃ (D : List DG) (N : Nat) (T : List Nat),
      SuOut D (List.replicate a 3) (List.replicate k 3 ++ 1 :: List.replicate c' 3) (0 + (nr - 1) + 1) T ∧
      znttLogic.Reach (loopSt (List.replicate a 3) (List.replicate k 3) (List.replicate c' 3) (nr - 1) p o os)
        (hdR QNTT.SU1 [] T) ∧
      znttLogic.Reach (hdR QNTT.SU1 [] T) (hdR QNTT.PA0 [3] (1 :: (List.replicate k 3 ++ 1 :: (List.replicate c' 3 ++ 1 ::
        (List.replicate (0 + (nr - 1) + 1 + 1) 3 ++ List.replicate (N + 1) 0)))))) := by
  have hO23 : ∀ O ∈ Os, O = 2 ∨ O = 3 := by
    intro O hO; rw [hOs] at hO; simp [List.mem_replicate] at hO; omega
  have hok : ∀ x ∈ o :: os, x.Ok := by rw [← ho]; exact initFrom_Ok p hp 0 Os hO23
  have hacc : ∀ x ∈ o :: os, 2 ≤ x.acc.length := by
    intro x hx; rw [← ho] at hx; rw [(initFrom_mem p (by omega) 0 Os x hx).1]; exact hp
  obtain ⟨D, hit, hl⟩ := assignLoop a k c' hk hc' n (nr - 1) (by omega) _ p o os rfl (by omega) hlen hok hacc
  rw [← ho] at hit
  rcases lp_circuit pr c nr n p Os hpr hcn hp hnr hnrN hOl hOs (List.replicate a 3) (List.replicate k 3)
    (List.replicate c' 3) _ hit hl with h | ⟨h1, N, T, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, D, N, T, h2⟩


end ZP.NTT




