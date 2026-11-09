module

public import ZP.SymExec

@[expose] public section

/-!
# Extending a logical machine

`M.Ext M'` says `M'` does everything `M` does and has the same beep state. Runs of `M` are
then runs of `M'`. This lets the lemmas proved for a base machine (`zp2` with the
machine-specific transitions removed) be used for each native machine.
-/

namespace ZP

def LTM.Ext (M M' : LTM) : Prop :=
  M.beep = M'.beep ∧ ∀ q a r, M.act q a = some r → M'.act q a = some r

theorem LTM.Ext.zstep {M M' : LTM} (h : M.Ext M') {c c' : ZC} (hs : M.zstep c = some c') :
    M'.zstep c = some c' := by
  unfold LTM.zstep at hs ⊢
  cases ha : M.act c.q (c.R 0) with
  | none => rw [ha] at hs; cases hs
  | some r =>
    rw [ha] at hs
    rw [h.2 _ _ _ ha]
    exact hs

theorem LTM.Ext.zrun {M M' : LTM} (h : M.Ext M') :
    ∀ (n : Nat) (c c' : ZC), M.zrun n c = some c' → M'.zrun n c = some c' := by
  intro n
  induction n with
  | zero => intro c c' hr; exact hr
  | succ n ih =>
    intro c c' hr
    show (if c.q = M'.beep then none else (M'.zstep c).bind (M'.zrun n)) = some c'
    have hr' : (if c.q = M.beep then none else (M.zstep c).bind (M.zrun n)) = some c' := hr
    by_cases hb : c.q = M.beep
    · rw [ite_eq_left hb] at hr'; cases hr'
    · have hb' : ¬ c.q = M'.beep := h.1 ▸ hb
      rw [ite_eq_right hb] at hr'
      rw [ite_eq_right hb']
      cases hz : M.zstep c with
      | none => rw [hz] at hr'; cases hr'
      | some d =>
        rw [hz] at hr'
        rw [h.zstep hz]
        exact ih d c' hr'

theorem LTM.Ext.reach {M M' : LTM} (h : M.Ext M') {c c' : ZC} (hr : M.Reach c c') :
    M'.Reach c c' := by
  obtain ⟨n, hn⟩ := hr
  exact ⟨n, h.zrun n c c' hn⟩

theorem LTM.Ext.reach1 {M M' : LTM} (h : M.Ext M') {c c' : ZC} (hr : M.Reach1 c c') :
    M'.Reach1 c c' := by
  obtain ⟨n, hn⟩ := hr
  exact ⟨n, h.zrun _ c c' hn⟩

theorem LTM.Ext.refl (M : LTM) : M.Ext M := ⟨rfl, fun _ _ _ h => h⟩

theorem LTM.Ext.trans {M M' M'' : LTM} (h : M.Ext M') (h' : M'.Ext M'') : M.Ext M'' :=
  ⟨h.1.trans h'.1, fun q a r hr => h'.2 q a r (h.2 q a r hr)⟩

/-! ## A decidable check for concrete machines -/

def LTM.code (M : LTM) (q a : Nat) : Nat := ((M.table.getD q []).getD a 0)

/-- Every defined entry of `M` is the same in `M'`, and the beep states agree. -/
def LTM.extB (M M' : LTM) : Bool :=
  M.beep == M'.beep &&
    (List.range M.table.length).all fun q =>
      (List.range (M.table.getD q []).length).all fun a =>
        M.code q a == 0 || M.code q a == M'.code q a

theorem LTM.act_eq_code (M : LTM) (q a : Nat) :
    M.act q a = (if M.code q a = 0 then none
      else some ((M.code q a - 1) % 4, (M.code q a - 1) / 4 % 2, (M.code q a - 1) / 8)) := by
  unfold LTM.act LTM.code
  cases h : M.table[q]? with
  | none => simp [h]
  | some row => simp [h]

theorem LTM.ext_of_extB {M M' : LTM} (h : M.extB M' = true) : M.Ext M' := by
  unfold LTM.extB at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at h
  obtain ⟨hb, hall⟩ := h
  refine ⟨hb, fun q a r hr => ?_⟩
  rw [LTM.act_eq_code] at hr
  have hne : M.code q a ≠ 0 := by
    intro h0
    rw [h0] at hr
    simp at hr
  have hq : q < M.table.length :=
    Classical.byContradiction fun hq => hne (by
      unfold LTM.code
      simp [List.getElem?_eq_none (by omega : M.table.length ≤ q)])
  have ha : a < (M.table.getD q []).length :=
    Classical.byContradiction fun ha => hne (by
      unfold LTM.code
      have h0 : (M.table.getD q []).length ≤ a := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h0]; rfl)
  have h2 := hall q hq a ha
  have heq : M.code q a = M'.code q a := by
    rcases h2 with h2 | h2
    · exact absurd h2 hne
    · exact h2
  rw [LTM.act_eq_code, ← heq]
  exact hr

end ZP
