module

public import ZP.UG

@[expose] public section

/-!
# A clocked simulation of a machine as a stack program

`SIM M` runs on stacks `[R, L, Q, C, A, ...]`: the tape of `M` as a zipper (`R` from
the head on, `L` left of the head reversed, a blank cell is an empty `R`), the state
`q` as `q` ones on `Q`, the clock as ones on `C`, and the answer on `A`. Each round
pops one clock tick and does one step of `M`: `DISP` finds row `q` by popping `Q`,
`ROW` branches on the scanned symbol, and `ACT` performs the action. A halting action
records the answer and clears the clock. `sim_ok`: after `T` ticks the answer stack
holds the answer of `zexec M T q L R` (a time-out answers no).
-/

namespace ZP.Cx

def SV (R L Q C A : List Bool) (X : List (List Bool)) : List (List Bool) := R :: L :: Q :: C :: A :: X

def pushN : Nat → Cmd
  | 0 => .skip
  | n + 1 => .seq (pushN n) (.push 2 true)

def hset : Bool → Cmd
  | true => .push 4 true
  | false => .skip

def mvd : Bool → Cmd
  | true => mv1 0 1
  | false => mv1 1 0

def ACT : Act → Cmd
  | .halt b => .seq (hset b) (clr 3)
  | .go w d q => .seq (.pop 0) (.seq (.push 0 w) (.seq (mvd d) (pushN q)))

def ROW (r : Act × Act × Act) : Cmd := .cs 0 (ACT r.1) (ACT r.2.1) (ACT r.2.2)

def DISP : List (Act × Act × Act) → Cmd
  | [] => ACT (.halt false)
  | r :: rs => .cs 2 (ROW r) .skip (.seq (.pop 2) (DISP rs))

def SIM (M : Mach) : Cmd := .wh 3 false true true (.seq (.pop 3) (DISP M.tbl))

/-! ## The actions -/

section
variable {R L Q C A : List Bool} {X : List (List Bool)}

theorem pushN_ok : ∀ (n : Nat) (Q : List Bool),
    ExecB (pushN n) (SV R L Q C A X) (SV R L (List.replicate n true ++ Q) C A X) (n + 1)
  | 0, Q => ExecB.skip.to rfl (Nat.le_refl _)
  | n + 1, Q => by
    have h1 := pushN_ok n Q
    have h2 : ExecB (.push 2 true) (SV R L (List.replicate n true ++ Q) C A X)
        (SV R L (List.replicate (n + 1) true ++ Q) C A X) 1 := ExecB.push.to rfl (Nat.le_refl _)
    exact (h1.seq h2).to rfl (by omega)

theorem act_halt (b : Bool) (T : Nat) :
    ExecB (ACT (.halt b)) (SV R L Q (List.replicate T true) [] X) (SV R L Q [] (ansOf b) X)
      (2 * T + 2) := by
  have h1 : ExecB (hset b) (SV R L Q (List.replicate T true) [] X)
      (SV R L Q (List.replicate T true) (ansOf b) X) 1 := by
    cases b
    · exact ExecB.skip
    · exact ExecB.push.to rfl (Nat.le_refl _)
  have h2 : ExecB (clr 3) (SV R L Q (List.replicate T true) (ansOf b) X)
      (SV R L Q [] (ansOf b) X) (2 * (List.replicate T true).length + 1) :=
    (clr_ok (i := 3) _ _ (by simp only [SV, List.length_cons]; omega) rfl).to rfl (Nat.le_refl _)
  rw [List.length_replicate] at h2
  exact (h1.seq h2).to rfl (by omega)

theorem act_go (w d : Bool) (q' : Nat) :
    ExecB (ACT (.go w d q')) (SV R L [] C A X)
      (SV (gmove d w L R).2 (gmove d w L R).1 (List.replicate q' true) C A X) (q' + 6) := by
  have h1 : ExecB (.pop 0) (SV R L [] C A X) (SV R.tail L [] C A X) 1 :=
    ExecB.pop.to rfl (Nat.le_refl _)
  have h2 : ExecB (.push 0 w) (SV R.tail L [] C A X) (SV (w :: R.tail) L [] C A X) 1 :=
    ExecB.push.to rfl (Nat.le_refl _)
  have h3 : ExecB (mvd d) (SV (w :: R.tail) L [] C A X)
      (SV (gmove d w L R).2 (gmove d w L R).1 [] C A X) 3 := by
    cases d with
    | true => exact (mv1_cons (by decide) rfl).to rfl (Nat.le_refl _)
    | false =>
      cases L with
      | nil => exact (mv1_nil rfl).to rfl (by omega)
      | cons b l => exact (mv1_cons (by decide) rfl).to rfl (Nat.le_refl _)
  have h4 := pushN_ok (R := (gmove d w L R).2) (L := (gmove d w L R).1) (C := C) (A := A) (X := X)
    q' []
  exact (h1.seq (h2.seq (h3.seq h4))).to (by rw [List.append_nil]) (by omega)

end

/-! ## Dispatch -/

def actOf (rows : List (Act × Act × Act)) (q : Nat) (s : Option Bool) : Act :=
  match rows[q]? with
  | none => .halt false
  | some r => pick r s

theorem actOf_nil (q : Nat) (s : Option Bool) : actOf [] q s = .halt false := by
  simp [actOf]

theorem actOf_zero (r : Act × Act × Act) (rs : List (Act × Act × Act)) (s : Option Bool) :
    actOf (r :: rs) 0 s = pick r s := by
  simp [actOf]

theorem actOf_succ (r : Act × Act × Act) (rs : List (Act × Act × Act)) (q : Nat)
    (s : Option Bool) : actOf (r :: rs) (q + 1) s = actOf rs q s := by
  simp [actOf]

theorem act_eq (M : Mach) (q : Nat) (s : Option Bool) : M.act q s = actOf M.tbl q s := by
  unfold Mach.act actOf
  cases M.tbl[q]? with
  | none => rfl
  | some r =>
    obtain ⟨a0, a1, a2⟩ := r
    cases s with
    | none => rfl
    | some b => cases b <;> rfl

theorem row_ok (r : Act × Act × Act) {R L Q C A : List Bool} {X : List (List Bool)}
    {S' : List (List Bool)} {B : Nat}
    (h : ExecB (ACT (pick r R.head?)) (SV R L Q C A X) S' B) :
    ExecB (ROW r) (SV R L Q C A X) S' (B + 1) := by
  apply ExecB.cs
  cases R with
  | nil => exact h
  | cons b R => cases b <;> exact h

theorem disp_ok : ∀ (rows : List (Act × Act × Act)) (q : Nat) {R L C A : List Bool}
    {X : List (List Bool)} {S' : List (List Bool)} {B : Nat},
    ExecB (ACT (actOf rows q R.head?))
      (SV R L (List.replicate (q - rows.length) true) C A X) S' B →
    ExecB (DISP rows) (SV R L (List.replicate q true) C A X) S' (B + 2 * q + 2)
  | [], q, R, L, C, A, X, S', B, h => by
    rw [actOf_nil, List.length_nil, Nat.sub_zero] at h
    have h' : ExecB (ACT (.halt false)) (SV R L (List.replicate q true) C A X) S' B := h
    exact h'.to rfl (by omega)
  | r :: rs, 0, R, L, C, A, X, S', B, h => by
    rw [Nat.zero_sub, actOf_zero] at h
    have h1 : ExecB (ROW r) (SV R L [] C A X) S' (B + 1) := row_ok r (by exact h)
    exact (ExecB.cs (by exact h1)).to rfl (by omega)
  | r :: rs, q + 1, R, L, C, A, X, S', B, h => by
    rw [List.length_cons, Nat.add_sub_add_right, actOf_succ] at h
    have ih := disp_ok rs q (R := R) (L := L) (C := C) (A := A) (X := X) (by exact h)
    have hp : ExecB (.pop 2) (SV R L (List.replicate (q + 1) true) C A X)
        (SV R L (List.replicate q true) C A X) 1 := ExecB.pop.to rfl (Nat.le_refl _)
    exact (ExecB.cs (by exact hp.seq ih)).to rfl (by omega)

/-! ## The bound on states -/

def aq : Act → Nat
  | .halt _ => 0
  | .go _ _ q => q

def rq (r : Act × Act × Act) : Nat := aq r.1 + aq r.2.1 + aq r.2.2

/-- A bound on every target state of `M`. -/
def qm (M : Mach) : Nat := (M.tbl.map rq).sum

theorem rq_le : ∀ (rows : List (Act × Act × Act)) (q : Nat) (r : Act × Act × Act),
    rows[q]? = some r → rq r ≤ (rows.map rq).sum
  | [], _, _, h => by simp at h
  | r' :: rs, 0, r, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp
  | r' :: rs, q + 1, r, h => by
    simp only [List.getElem?_cons_succ] at h
    have := rq_le rs q r h
    simp only [List.map_cons, List.sum_cons]
    omega

theorem actOf_go {rows : List (Act × Act × Act)} {q : Nat} {s : Option Bool} {w d : Bool}
    {q' : Nat} (h : actOf rows q s = .go w d q') :
    q < rows.length ∧ q' ≤ (rows.map rq).sum := by
  unfold actOf at h
  cases hr : rows[q]? with
  | none => rw [hr] at h; cases h
  | some r =>
    rw [hr] at h
    refine ⟨?_, ?_⟩
    · rcases Nat.lt_or_ge q rows.length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at hr
        cases hr
    · have h1 := rq_le rows q r hr
      have h2 : q' ≤ rq r := by
        obtain ⟨a0, a1, a2⟩ := r
        unfold rq
        cases s with
        | none => simp only [pick] at h; subst h; simp only [aq]; omega
        | some b =>
          cases b
          · simp only [pick] at h; subst h; simp only [aq]; omega
          · simp only [pick] at h; subst h; simp only [aq]; omega
      omega

/-! ## The simulation -/

theorem zexec_gmove {M : Mach} {T q : Nat} {L R : List Bool} {w d : Bool} {q' : Nat}
    (h : M.act q R.head? = .go w d q') :
    zexec M (T + 1) q L R = zexec M T q' (gmove d w L R).1 (gmove d w L R).2 := by
  cases d with
  | true => exact zexec_goR h
  | false =>
    cases L with
    | nil => exact zexec_goL0 h
    | cons b l => exact zexec_goL h

/-- A bound on one simulated step with `T` ticks left. -/
def sB (M : Mach) (T : Nat) : Nat := 2 * T + 3 * qm M + 10

theorem gmove_len (d w : Bool) (L R : List Bool) :
    (gmove d w L R).2.length + (gmove d w L R).1.length ≤ R.length + L.length + 1 := by
  cases d with
  | true => simp [gmove] <;> omega
  | false =>
    cases L with
    | nil => simp [gmove] <;> omega
    | cons b l => simp [gmove] <;> omega

theorem sim_ok (M : Mach) (X : List (List Bool)) : ∀ (T q : Nat) (L R : List Bool), q ≤ qm M →
    ∃ R' L' Q', R'.length + L'.length ≤ R.length + L.length + T ∧
      ExecB (SIM M) (SV R L (List.replicate q true) (List.replicate T true) [] X)
        (SV R' L' Q' [] (ansOf ((zexec M T q L R).getD false)) X) (T * (sB M T + 2) + 1)
  | 0, q, L, R, _ =>
    ⟨R, L, List.replicate q true, by omega, ExecB.to (ExecB.whF (by rfl)) rfl (by omega)⟩
  | T + 1, q, L, R, hq => by
    have hmono : sB M T ≤ sB M (T + 1) := by unfold sB; omega
    have b1 : ExecB (.pop 3) (SV R L (List.replicate q true) (List.replicate (T + 1) true) [] X)
        (SV R L (List.replicate q true) (List.replicate T true) [] X) 1 :=
      ExecB.pop.to rfl (Nat.le_refl _)
    cases ha : actOf M.tbl q R.head? with
    | halt b =>
      have hz : zexec M (T + 1) q L R = some b := zexec_halt (by rw [act_eq]; exact ha)
      rw [hz]
      have h0 := act_halt (R := R) (L := L) (Q := List.replicate (q - M.tbl.length) true) (X := X)
        b T
      rw [← ha] at h0
      have b2 := disp_ok M.tbl q h0
      refine ⟨R, L, List.replicate (q - M.tbl.length) true, by omega, (ExecB.whT (i := 3) (me := false) (mf := true) (mt := true) (by rfl)
        (b1.seq b2) (ExecB.whF (by rfl))).to rfl ?_⟩
      have := main_bound (sB M T) (sB M (T + 1)) T hmono
      have h3 : 2 * T + 2 + 2 * q + 2 ≤ sB M T := by unfold sB; omega
      omega
    | go w d q' =>
      obtain ⟨hq1, hq2⟩ := actOf_go ha
      have hz : zexec M (T + 1) q L R = zexec M T q' (gmove d w L R).1 (gmove d w L R).2 :=
        zexec_gmove (by rw [act_eq]; exact ha)
      rw [hz]
      have h0 : ExecB (ACT (actOf M.tbl q R.head?))
          (SV R L (List.replicate (q - M.tbl.length) true) (List.replicate T true) [] X)
          (SV (gmove d w L R).2 (gmove d w L R).1 (List.replicate q' true) (List.replicate T true)
            [] X) (q' + 6) := by
        rw [ha, show q - M.tbl.length = 0 by omega]
        exact act_go w d q'
      have b2 := disp_ok M.tbl q h0
      obtain ⟨R', L', Q', hl, ih⟩ := sim_ok M X T q' (gmove d w L R).1 (gmove d w L R).2 hq2
      have hg := gmove_len d w L R
      refine ⟨R', L', Q', by omega, (ExecB.whT (by rfl) (b1.seq b2) ih).to rfl ?_⟩
      have := main_bound (sB M T) (sB M (T + 1)) T hmono
      have hq3 : q' ≤ qm M := hq2
      have h3 : q' + 6 + 2 * q + 2 ≤ sB M T := by unfold sB; omega
      omega

/-! ## Stack indices -/

theorem ok_pushN {k : Nat} (hk : 5 ≤ k) : ∀ n, Ok k (pushN n)
  | 0 => trivial
  | n + 1 => ⟨ok_pushN hk n, (by omega : 2 < k)⟩

theorem ok_ACT {k : Nat} (hk : 5 ≤ k) : ∀ a, Ok k (ACT a)
  | .halt b => by
    cases b
    · exact ⟨trivial, (by omega : 3 < k), (by omega : 3 < k)⟩
    · exact ⟨(by omega : 4 < k), (by omega : 3 < k), (by omega : 3 < k)⟩
  | .go w d q => by
    refine ⟨(by omega : 0 < k), (by omega : 0 < k), ?_, ok_pushN hk q⟩
    cases d
    · exact ⟨(by omega : 1 < k), trivial, ⟨(by omega : 1 < k), (by omega : 0 < k)⟩,
        ⟨(by omega : 1 < k), (by omega : 0 < k)⟩⟩
    · exact ⟨(by omega : 0 < k), trivial, ⟨(by omega : 0 < k), (by omega : 1 < k)⟩,
        ⟨(by omega : 0 < k), (by omega : 1 < k)⟩⟩

theorem ok_DISP {k : Nat} (hk : 5 ≤ k) : ∀ rows, Ok k (DISP rows)
  | [] => ok_ACT hk _
  | r :: rs => ⟨(by omega : 2 < k), ⟨(by omega : 0 < k), ok_ACT hk _, ok_ACT hk _, ok_ACT hk _⟩,
      trivial, (by omega : 2 < k), ok_DISP hk rs⟩

theorem ok_SIM {k : Nat} (hk : 5 ≤ k) (M : Mach) : Ok k (SIM M) :=
  ⟨(by omega : 3 < k), (by omega : 3 < k), ok_DISP hk M.tbl⟩

end ZP.Cx
