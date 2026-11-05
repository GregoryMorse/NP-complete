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

end ZP.G
