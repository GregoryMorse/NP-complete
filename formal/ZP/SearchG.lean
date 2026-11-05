module

public import ZP.PairG

@[expose] public section

/-! # The search of the GI machine: the abstract depth-first enumeration -/

namespace ZP.G

open ZP

/-- The depth-first search from the stack `rest` with candidate `c` on top: `b = true` iff a stack
passing `chk` is found; `false` iff the whole subtree fails (control returns to the parent). -/
inductive Rch (chk : List Nat → Bool) (m : Nat) : List Nat → Nat → Bool → Prop
  | z_ok {rest : List Nat} : chk rest = true → Rch chk m rest 0 true
  | z_no {rest : List Nat} : chk rest = false → Rch chk m rest 0 false
  | coll {rest : List Nat} {c : Nat} {b : Bool} : (c + 1) ∈ rest → Rch chk m rest c b → Rch chk m rest (c + 1) b
  | push_ok {rest : List Nat} {c : Nat} : (c + 1) ∉ rest → Rch chk m ((c + 1) :: rest) m true → Rch chk m rest (c + 1) true
  | push_no {rest : List Nat} {c : Nat} {b : Bool} : (c + 1) ∉ rest → Rch chk m ((c + 1) :: rest) m false →
      Rch chk m rest c b → Rch chk m rest (c + 1) b

/-- Unused values. -/
def unused (m : Nat) (rest : List Nat) : Nat :=
  ((List.range m).filter fun i => !rest.contains (i + 1)).length

theorem unused_push (m c : Nat) (rest : List Nat) (hc : c + 1 ≤ m) (hn : (c + 1) ∉ rest) :
    unused m ((c + 1) :: rest) < unused m rest := by
  unfold unused
  have e : ((List.range m).filter fun i => !((c + 1) :: rest).contains (i + 1))
      = ((List.range m).filter fun i => !rest.contains (i + 1)).filter fun i => i != c := by
    rw [List.filter_filter]
    congr 1
    funext i
    simp only [List.contains_cons, Bool.not_or]
    have : (!(i + 1 == c + 1)) = (i != c) := by
      by_cases h : i = c
      · subst h; simp
      · have h1 : (i + 1 == c + 1) = false := beq_false_of_ne (by omega)
        have h2 : (i != c) = true := bne_iff_ne.2 h
        simp [h1, h2]
    rw [this]
  rw [e, List.length_filter_lt_length_iff_exists]
  refine ⟨c, ?_, by simp⟩
  rw [List.mem_filter]
  refine ⟨List.mem_range.2 (by omega), ?_⟩
  simp [List.contains_iff_mem, hn]

def VStack (m : Nat) (rest : List Nat) : Prop := rest.Nodup ∧ ∀ e ∈ rest, 1 ≤ e ∧ e ≤ m

/-- The stacks examined (and checked) while the search is at `rest` with candidate `c`. -/
def Expl (m : Nat) (rest : List Nat) (c : Nat) (s : List Nat) : Prop :=
  s = rest ∨ ∃ t0 x, s = t0 ++ x :: rest ∧ x ≤ c ∧ VStack m s

theorem vstack_push {m c : Nat} {rest : List Nat} (hv : VStack m rest) (hc : c + 1 ≤ m) (hn : (c + 1) ∉ rest) :
    VStack m ((c + 1) :: rest) := by
  refine ⟨List.nodup_cons.2 ⟨hn, hv.1⟩, fun e he => ?_⟩
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨by omega, hc⟩
  · exact hv.2 e he

theorem expl_zero {m : Nat} {rest s : List Nat} (hv : VStack m rest) : Expl m rest 0 s ↔ s = rest := by
  constructor
  · rintro (h | ⟨t0, x, hs, hx, hvs⟩)
    · exact h
    · exfalso
      have : x ∈ s := by rw [hs]; simp
      have := (hvs.2 x this).1
      omega
  · intro h; exact Or.inl h

theorem expl_coll {m c : Nat} {rest s : List Nat} (hv : VStack m rest) (hm : (c + 1) ∈ rest) :
    Expl m rest (c + 1) s ↔ Expl m rest c s := by
  constructor
  · rintro (h | ⟨t0, x, hs, hx, hvs⟩)
    · exact Or.inl h
    · refine Or.inr ⟨t0, x, hs, ?_, hvs⟩
      cases Nat.lt_or_ge c x with
      | inl hlt =>
        exfalso
        have hxe : x = c + 1 := by omega
        subst hxe
        have hnd := hvs.1
        rw [hs] at hnd
        have := (List.nodup_append.1 hnd).2.1
        have h2 := List.nodup_cons.1 this
        exact h2.1 hm
      | inr hge => omega
  · rintro (h | ⟨t0, x, hs, hx, hvs⟩)
    · exact Or.inl h
    · exact Or.inr ⟨t0, x, hs, by omega, hvs⟩

theorem expl_push {m c : Nat} {rest s : List Nat} (hv : VStack m rest) (hc : c + 1 ≤ m) (hn : (c + 1) ∉ rest) :
    Expl m rest (c + 1) s ↔ Expl m rest c s ∨ Expl m ((c + 1) :: rest) m s := by
  constructor
  · rintro (h | ⟨t0, x, hs, hx, hvs⟩)
    · exact Or.inl (Or.inl h)
    · by_cases hxc : x ≤ c
      · exact Or.inl (Or.inr ⟨t0, x, hs, hxc, hvs⟩)
      · have hxe : x = c + 1 := by omega
        subst hxe
        right
        rcases List.eq_nil_or_concat t0 with h0 | ⟨t1, y, h0⟩
        · subst h0; exact Or.inl hs
        · refine Or.inr ⟨t1, y, ?_, ?_, hvs⟩
          · rw [hs, h0]; simp
          · have hy : y ∈ s := by rw [hs, h0]; simp
            exact (hvs.2 y hy).2
  · rintro (h | h)
    · rcases h with h | ⟨t0, x, hs, hx, hvs⟩
      · exact Or.inl h
      · exact Or.inr ⟨t0, x, hs, by omega, hvs⟩
    · rcases h with h | ⟨t1, y, hs, hy, hvs⟩
      · exact Or.inr ⟨[], c + 1, by rw [h]; rfl, Nat.le_refl _, h ▸ vstack_push hv hc hn⟩
      · exact Or.inr ⟨t1 ++ [y], c + 1, by rw [hs]; simp, Nat.le_refl _, hvs⟩

theorem Rch_sem {chk : List Nat → Bool} {m : Nat} {rest : List Nat} {c : Nat} {b : Bool}
    (h : Rch chk m rest c b) : VStack m rest → c ≤ m →
    (b = true ↔ ∃ s, Expl m rest c s ∧ chk s = true) := by
  induction h with
  | z_ok hk =>
    intro hv _
    exact ⟨fun _ => ⟨_, Or.inl rfl, hk⟩, fun _ => rfl⟩
  | z_no hk =>
    intro hv _
    constructor
    · intro h; cases h
    · rintro ⟨s, hs, hc⟩
      rw [expl_zero hv] at hs
      rw [hs] at hc
      rw [hk] at hc; cases hc
  | @coll rest c b hm _ ih =>
    intro hv hc
    rw [ih hv (by omega)]
    constructor
    · rintro ⟨s, hs, hk⟩; exact ⟨s, (expl_coll hv hm).2 hs, hk⟩
    · rintro ⟨s, hs, hk⟩; exact ⟨s, (expl_coll hv hm).1 hs, hk⟩
  | @push_ok rest c hn _ ih =>
    intro hv hc
    have hv' := vstack_push hv hc hn
    obtain ⟨s, hs, hk⟩ := (ih hv' (Nat.le_refl _)).1 rfl
    exact ⟨fun _ => ⟨s, (expl_push hv hc hn).2 (Or.inr hs), hk⟩, fun _ => rfl⟩
  | @push_no rest c b hn _ _ ih1 ih2 =>
    intro hv hc
    have hv' := vstack_push hv hc hn
    have h2 := ih2 hv (by omega)
    constructor
    · intro hb
      obtain ⟨s, hs, hk⟩ := h2.1 hb
      exact ⟨s, (expl_push hv hc hn).2 (Or.inl hs), hk⟩
    · rintro ⟨s, hs, hk⟩
      rcases (expl_push hv hc hn).1 hs with hs | hs
      · exact h2.2 ⟨s, hs, hk⟩
      · exfalso
        have := (ih1 hv' (Nat.le_refl _)).2 ⟨s, hs, hk⟩
        cases this

theorem Rch_total (chk : List Nat → Bool) (m : Nat) : ∀ u rest c, unused m rest = u → VStack m rest → c ≤ m →
    ∃ b, Rch chk m rest c b := by
  intro u
  induction u using Nat.strongRecOn with
  | _ u ihu =>
    intro rest c hu hv hc
    induction c with
    | zero =>
      cases hk : chk rest
      · exact ⟨false, Rch.z_no hk⟩
      · exact ⟨true, Rch.z_ok hk⟩
    | succ c ihc =>
      by_cases hm : (c + 1) ∈ rest
      · obtain ⟨b, hb⟩ := ihc (by omega)
        exact ⟨b, Rch.coll hm hb⟩
      · have hv' := vstack_push hv hc hm
        have hlt : unused m ((c + 1) :: rest) < u := by rw [← hu]; exact unused_push m c rest hc hm
        obtain ⟨b1, hb1⟩ := ihu _ hlt ((c + 1) :: rest) m rfl hv' (Nat.le_refl _)
        cases b1
        · obtain ⟨b, hb⟩ := ihc (by omega)
          exact ⟨b, Rch.push_no hm hb1 hb⟩
        · exact ⟨true, Rch.push_ok hm hb1⟩

/-! ## The machine side of the search -/

structure GEnv where
  m : Nat
  Tc : List Nat
  Z : List Nat
  z : Nat
  Z' : List Nat
  hT : Tc ++ 0 :: Z = List.replicate m 3 ++ (z :: Z')
  hz : z = 0 ∨ z = 1
  hZ' : Sym4 Z'
  hTc : ∀ a ∈ Tc, a ∈ O13
  hZ : Sym4 Z

namespace GEnv

def Rt (E : GEnv) : List Nat := 1 :: (E.Tc ++ 0 :: E.Z)

def CfgS (E : GEnv) (rest : List Nat) (c : Nat) : ZC :=
  hdR QG.gDP [] (List.replicate c 3 ++ 1 :: (Enc rest ++ E.Rt))

def CfgD (E : GEnv) (rest : List Nat) : ZC := hdR QG.gDC [] (Enc rest ++ E.Rt)

def CfgPop (E : GEnv) (rest : List Nat) : ZC := hdR QG.gGL [0] (Enc rest ++ E.Rt)

theorem Rt_sym4 (E : GEnv) : Sym4 E.Rt := by
  have := o13_sym4 E.hTc
  simp [Rt, ALL, this, E.hZ]

theorem pop (E : GEnv) (rest : List Nat) : zgiLogic.Reach (E.CfgS rest 0) (E.CfgPop rest) := by
  have h := gdpPop (Enc rest ++ E.Rt) (by simp [E.Rt_sym4])
  exact h.of_eq (by simp [CfgS]) (by simp [CfgPop])

theorem dec (E : GEnv) (c : Nat) (rest : List Nat) :
    zgiLogic.Reach (E.CfgD ((c + 1) :: rest)) (E.CfgS rest c) := by
  have h := gdcDec (List.replicate c 3 ++ 1 :: (Enc rest ++ E.Rt)) (by simp [E.Rt_sym4, ALL])
  refine (h.of_eq (by simp [CfgD, Enc, U, List.replicate_succ]) rfl).trans ?_
  have e : hdR QG.gDP [0] (List.replicate c 3 ++ 1 :: (Enc rest ++ E.Rt)) = E.CfgS rest c := by
    unfold CfgS
    exact F.hdR_zeros QG.gDP [0] [] _ (fun a ha => by simp at ha; simp [F.B0, ha])
  rw [e]
  exact LTM.Reach.refl _ _

theorem scanColl (E : GEnv) (c : Nat) (rest : List Nat) (hr : ∀ e ∈ rest, 1 ≤ e) (hm : (c + 1) ∈ rest) :
    zgiLogic.Reach (E.CfgS rest (c + 1)) (E.CfgD ((c + 1) :: rest)) := by
  have h1 := gdpTop [] (List.replicate c 3 ++ 1 :: (Enc rest ++ E.Rt)) (by simp [ALL]) (by simp [E.Rt_sym4, ALL])
  have h2 := gkeTop [3] (List.replicate c 3) (Enc rest ++ E.Rt) (by simp [ALL]) (bits_rep3 c) (by simp [E.Rt_sym4])
  have h3 := (scanLoop (c + 1) E.Tc E.Z E.hTc E.hZ rest [] hr (by simp) (by omega)).2 hm
  unfold CfgS CfgD Rt
  unfold Rt at h1 h2
  simp only [List.replicate_succ, List.append_assoc, Enc, U, MEnc, List.nil_append, List.singleton_append,
    List.cons_append] at h1 h2 h3 ⊢
  exact h1.trans (h2.trans h3)

theorem scanPush (E : GEnv) (c : Nat) (rest : List Nat) (hr : ∀ e ∈ rest, 1 ≤ e) (hm : (c + 1) ∉ rest) :
    zgiLogic.Reach (E.CfgS rest (c + 1)) (E.CfgS ((c + 1) :: rest) E.m) := by
  have h1 := gdpTop [] (List.replicate c 3 ++ 1 :: (Enc rest ++ E.Rt)) (by simp [ALL]) (by simp [E.Rt_sym4, ALL])
  have h2 := gkeTop [3] (List.replicate c 3) (Enc rest ++ E.Rt) (by simp [ALL]) (bits_rep3 c) (by simp [E.Rt_sym4])
  have h3 := (scanLoop (c + 1) E.Tc E.Z E.hTc E.hZ rest [] hr (by simp) (by omega)).1 hm
  have hnb : NoB (List.replicate (c + 1) 3 ++ [1] ++ MEnc ([] ++ rest)) := by simp [NB]
  have h4 := gupWalk _ (1 :: (E.Tc ++ 0 :: E.Z)) hnb (by simpa [Rt] using E.Rt_sym4)
  have hr' : ∀ v ∈ (c + 1) :: rest, 1 ≤ v := by
    intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · omega
    · exact hr v hv
  have h5 := pushAll E.m ((c + 1) :: rest) E.Z' E.z E.hz hr' E.hZ'
  have hu : unm (List.replicate (c + 1) 3 ++ [1] ++ MEnc ([] ++ rest)) = Enc ((c + 1) :: rest) := by
    simp [unm_MEnc, Enc, U, unm1]
  rw [hu] at h4
  have hT := E.hT
  unfold CfgS Rt
  rw [← hT] at h5
  unfold Rt at h1 h2
  simp only [List.replicate_succ, List.append_assoc, Enc, U, MEnc, List.nil_append, List.singleton_append,
    List.cons_append] at h1 h2 h3 h4 h5 ⊢
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

end GEnv

namespace GEnv

/-- The check phase: from the popped stack the machine either accepts or returns to the decrement. -/
def CheckSpec (E : GEnv) (chk : List Nat → Bool) (Acc : ZC) : Prop :=
  ∀ rest, VStack E.m rest →
    (chk rest = true → zgiLogic.Reach (E.CfgPop rest) Acc) ∧
    (chk rest = false → zgiLogic.Reach (E.CfgPop rest) (E.CfgD rest))

theorem search_machine (E : GEnv) (chk : List Nat → Bool) (Acc : ZC) (hC : E.CheckSpec chk Acc)
    {rest : List Nat} {c : Nat} {b : Bool} (h : Rch chk E.m rest c b) :
    VStack E.m rest → c ≤ E.m →
    (b = true → zgiLogic.Reach (E.CfgS rest c) Acc) ∧
    (b = false → zgiLogic.Reach (E.CfgS rest c) (E.CfgD rest)) := by
  induction h with
  | @z_ok rest hk =>
    intro hv _
    exact ⟨fun _ => (E.pop rest).trans ((hC rest hv).1 hk), fun h => by cases h⟩
  | @z_no rest hk =>
    intro hv _
    exact ⟨fun h => (by cases h), fun _ => (E.pop rest).trans ((hC rest hv).2 hk)⟩
  | @coll rest c b hm _ ih =>
    intro hv hc
    have hr : ∀ e ∈ rest, 1 ≤ e := fun e he => (hv.2 e he).1
    have hs := (E.scanColl c rest hr hm).trans (E.dec c rest)
    obtain ⟨i1, i2⟩ := ih hv (by omega)
    exact ⟨fun hb => hs.trans (i1 hb), fun hb => hs.trans (i2 hb)⟩
  | @push_ok rest c hn _ ih =>
    intro hv hc
    have hr : ∀ e ∈ rest, 1 ≤ e := fun e he => (hv.2 e he).1
    have hs := E.scanPush c rest hr hn
    have hv' := vstack_push hv hc hn
    exact ⟨fun _ => hs.trans ((ih hv' (Nat.le_refl _)).1 rfl), fun h => by cases h⟩
  | @push_no rest c b hn _ _ ih1 ih2 =>
    intro hv hc
    have hr : ∀ e ∈ rest, 1 ≤ e := fun e he => (hv.2 e he).1
    have hs := E.scanPush c rest hr hn
    have hv' := vstack_push hv hc hn
    have hs2 := hs.trans (((ih1 hv' (Nat.le_refl _)).2 rfl).trans (E.dec c rest))
    obtain ⟨i1, i2⟩ := ih2 hv (by omega)
    exact ⟨fun hb => hs2.trans (i1 hb), fun hb => hs2.trans (i2 hb)⟩

end GEnv

theorem injL_mem (m : Nat) : ∀ t w, w ∈ injL m t ↔ w.length = t ∧ w.Nodup ∧ ∀ v ∈ w, 1 ≤ v ∧ v ≤ m := by
  intro t
  induction t with
  | zero =>
    intro w
    simp only [injL, List.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, -, -⟩; exact List.length_eq_zero_iff.1 h
  | succ t ih =>
    intro w
    simp only [injL, List.mem_flatMap, List.mem_filterMap, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨w0, hw0, i, ⟨a, ha, rfl⟩, hv⟩
      by_cases hm : (a + 1) ∈ w0
      · simp [hm] at hv
      have hn : (a + 1) ∉ w0 := hm
      simp [hm] at hv
      subst hv
      obtain ⟨hl, hnd, hr⟩ := (ih w0).1 hw0
      refine ⟨by simp [hl], ?_, ?_⟩
      · rw [List.nodup_append]
        exact ⟨hnd, by simp, fun x hx y hy hxy => by simp at hy; subst hy; subst hxy; exact hn hx⟩
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hr x hx
        · simp at hx; subst hx; omega
    · rintro ⟨hl, hnd, hr⟩
      rcases List.eq_nil_or_concat w with h0 | ⟨w0, v, hw⟩
      · subst h0; simp at hl
      · subst hw
        have hl0 : w0.length = t := by simpa using hl
        have hnd' := (List.nodup_append.1 (by simpa using hnd)).1
        have hn : v ∉ w0 := by
          have := (List.nodup_append.1 (by simpa using hnd)).2.2
          intro hv; exact this v hv v (by simp) rfl
        have hrv : 1 ≤ v ∧ v ≤ m := hr v (by simp)
        refine ⟨w0, (ih w0).2 ⟨hl0, hnd', fun x hx => hr x (by simp [hx])⟩, v, ⟨v - 1, by omega, by omega⟩, ?_⟩
        simp [hn]

theorem vlen : ∀ (m : Nat) (w : List Nat), w.Nodup → (∀ v ∈ w, 1 ≤ v ∧ v ≤ m) → w.length ≤ m := by
  intro m
  induction m with
  | zero =>
    intro w _ h
    cases w with
    | nil => simp
    | cons a w => have := h a (List.mem_cons_self ..); omega
  | succ m ih =>
    intro w hnd h
    by_cases hm : (m + 1) ∈ w
    · have h1 := ih (w.erase (m + 1)) (hnd.erase _) (by
        intro v hv
        have hne : v ≠ m + 1 := (List.Nodup.mem_erase_iff hnd).1 hv |>.1
        have hv' := (List.Nodup.mem_erase_iff hnd).1 hv |>.2
        have := h v hv'
        omega)
      rw [List.length_erase_of_mem hm] at h1
      have : 0 < w.length := List.length_pos_of_mem hm
      omega
    · exact Nat.le_succ_of_le (ih w hnd (fun v hv => by
        have := h v hv
        have : v ≠ m + 1 := fun e => hm (e ▸ hv)
        omega))

/-- The search result is `inLG`. -/
theorem inLG_iff_Rch (s : List Bool) (b : Bool)
    (h : Rch (fun st => checkG st (parseG s).1 (parseG s).2.1 (parseG s).2.2) (parseG s).1 [] (parseG s).1 b) :
    b = true ↔ inLG s = true := by
  rw [Rch_sem h ⟨List.nodup_nil, by simp⟩ (Nat.le_refl _)]
  unfold inLG
  simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨st, hex, hk⟩
    have hv : VStack (parseG s).1 st := by
      rcases hex with rfl | ⟨t0, x, hs, hx, hvs⟩
      · exact ⟨List.nodup_nil, by simp⟩
      · exact hvs
    refine ⟨st.length, Nat.lt_succ_of_le (vlen _ st hv.1 hv.2), st, (injL_mem _ _ _).2 ⟨rfl, hv.1, hv.2⟩, hk⟩
  · rintro ⟨t, ht, w, hw, hk⟩
    obtain ⟨hl, hnd, hr⟩ := (injL_mem _ _ _).1 hw
    refine ⟨w, ?_, hk⟩
    cases w with
    | nil => exact Or.inl rfl
    | cons a w' =>
      obtain ⟨t0, x, hw'⟩ : ∃ t0 x, a :: w' = t0 ++ [x] := by
        rcases List.eq_nil_or_concat (a :: w') with h | ⟨t0, x, h⟩
        · exact absurd h (by simp)
        · exact ⟨t0, x, by simpa using h⟩
      refine Or.inr ⟨t0, x, hw', ?_, hnd, hr⟩
      have : x ∈ a :: w' := by rw [hw']; simp
      exact (hr x this).2

end ZP.G
