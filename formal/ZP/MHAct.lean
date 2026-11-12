module

public import ZP.MHStore

@[expose] public section

/-!
# Multihead act: the storage operations (shared by `Z_LP` and `Z_LNL`)

An act is entered at `G2 w d` right of `H` (after the peek `GH w d` and its one step), on

    Qc 0^g 0 0 H  | Y  0  S          (c blank: the count-down emptied it)

where `Y = M_g ... end of the fuel` has no blank and `S = storeOf x pos cur` is the storage
(`ZP/MHStore.lean`). It ends in `RTW` on the last cell of `Qc`, with the new scanned symbol written into
`c` and the storage `storeOf x pos' cur'` of the head positions after the step of `ref/zmh_ref.py`:

* `w = 1`: the current head's position moves right (`d`, clamped at `|x|+1`) or left (clamped at `0`);
* `w = 0`: the current head becomes the next one (`d`, towards `|P|`) or the previous one (towards `0`).

The segment lemmas are generated (`ZP/MHActSeg.lean`); this file assembles them. Main results:
`carrySem` (read and carry), `actMR actML actLS actRS` (one operation each) and `act` (all four,
for `storeOf`).
-/

namespace ZP.MH

open ZP

/-! ## Facts about `take` and `drop` -/

theorem take_succ_app (u : List Nat) (i : Nat) (h : i < u.length) : u.take (i + 1) = u.take i ++ [u[i]] := by
  rw [List.take_succ, List.getElem?_eq_getElem h]
  rfl

theorem NoB.one_app {S : List Nat} (hS : NoB S) (T : List Nat) (hT : NoB T) : NoB (S ++ T) := hS.app hT

theorem NoB.single {a : Nat} (h : a ∈ NB) : NoB [a] := NoB.cons h NoB.nil

theorem NoB.one_cons (u : List Nat) (hu : Bits u) : NoB (1 :: u) := NoB.cons (by simp [NB]) hu.noB

theorem NoB.take {u : List Nat} (hu : NoB u) (n : Nat) : NoB (u.take n) :=
  fun a ha => hu a (List.mem_of_mem_take ha)

/-! ## Read and carry -/

/-- From `RR` right of the marker: read the scanned cell (position `q`) and write it into `c`. The storage is
`SL`, the unit of position `q`, `SR` (empty or starting with `M`). -/
theorem carrySem (Qc Y SL SR u : List Nat) (g q : Nat) (hQ : Bits Qc) (hY : NoB Y) (hS : NoB SL)
    (hu : Bits u) (hq : q ≤ u.length) (hSR : SR = [] ∨ ∃ S, SR = 1 :: S) (hSR4 : Sym4 SR) :
    mhBase.Reach
      (hdR QMH.RR (Qc ++ List.replicate g 0 ++ [0, 0, 1] ++ Y ++ 0 :: (SL ++ 1 :: u.take q ++ [0]))
        (u.drop q ++ SR))
      (hd Q.RTW Qc (List.replicate g 0 ++ 0 :: rdCell u q :: 1 :: (Y ++ 0 :: (SL ++ uc u q 0 ++ SR)))) := by
  by_cases hqe : q = u.length
  · subst hqe
    have hX : NoB (SL ++ 1 :: u) := hS.app (NoB.one_cons u hu)
    have e1 : rdCell u u.length = 0 := by simp [rdCell]
    rw [e1, List.drop_length, List.take_length]
    rcases hSR with rfl | ⟨S, rfl⟩
    · refine (carryN0 Qc Y (SL ++ 1 :: u) g hQ hY hX).ofEq ?_ ?_
      · exact hdR_eq (by simp) (by simp)
      · exact hd_eq rfl (by simp [uc])
    · have hS4 : Sym4 S := fun a ha => hSR4 a (List.mem_cons_of_mem _ ha)
      refine (carryN1 Qc Y (SL ++ 1 :: u) S g hQ hY hX hS4).ofEq ?_ ?_
      · exact hdR_eq (by simp) (by simp)
      · exact hd_eq rfl (by simp [uc])
  · have hlt : q < u.length := Nat.lt_of_le_of_ne hq hqe
    rw [List.drop_eq_getElem_cons hlt]
    have heb : u[q] ∈ bits := hu _ (List.getElem_mem hlt)
    have hdr4 : Sym4 (u.drop (q + 1) ++ SR) :=
      (hu.sym4.app (Sym4.nil)).app hSR4 |> fun _ =>
        Sym4.app (fun a ha => hu.sym4 a (List.mem_of_mem_drop ha)) hSR4
    cases q with
    | zero =>
      have e1 : rdCell u 0 = 0 := by simp [rdCell]
      rw [e1]
      refine (carryM Qc Y SL (u.drop 1 ++ SR) g u[0] heb hQ hY hS hdr4).ofEq ?_ ?_
      · exact hdR_eq (by simp) (by simp)
      · exact hd_eq rfl (by simp [uc, List.drop_eq_getElem_cons hlt])
    | succ q =>
      have hq1 : q < u.length := by omega
      have e1 : rdCell u (q + 1) = u[q] := by
        simp [rdCell, List.getD, List.getElem?_eq_getElem hq1, hqe]
      have hab : u[q] ∈ bits := hu _ (List.getElem_mem hq1)
      have hX : NoB (SL ++ 1 :: u.take q) := hS.app (NoB.one_cons _ (fun a ha => hu a (List.mem_of_mem_take ha)))
      rw [e1]
      refine (carryA Qc Y (SL ++ 1 :: u.take q) (u.drop (q + 1 + 1) ++ SR) g u[q] u[q + 1] hab heb hQ hY hX
        (by
          have : Sym4 (u.drop (q + 1 + 1)) := fun a ha => hu.sym4 a (List.mem_of_mem_drop ha)
          exact this.app hSR4)).ofEq ?_ ?_
      · simp only [take_succ_app u q hq1, List.append_assoc, List.cons_append, List.nil_append,
          List.singleton_append]
      · simp only [uc, take_succ_app u q hq1, List.drop_eq_getElem_cons hlt, List.append_assoc,
          List.cons_append, List.nil_append]

/-! ## The four operations -/

/-- Close the list equalities between the `hd`/`hdR` configurations of a composition, using the local
rewrite hypotheses. -/
macro "closeEq" : tactic =>
  `(tactic| all_goals first
    | exact hdR_eq (by simp only [cfg, uc, *, List.append_assoc, List.cons_append, List.nil_append,
        List.singleton_append, List.take_zero, List.drop_zero, List.append_nil]) (by simp only [cfg, uc, *, List.append_assoc, List.cons_append, List.nil_append,
        List.singleton_append, List.take_zero, List.drop_zero, List.append_nil])
    | exact hd_eq (by simp only [cfg, uc, *, List.append_assoc, List.cons_append, List.nil_append,
        List.singleton_append, List.take_zero, List.drop_zero, List.append_nil]) (by simp only [cfg, uc, *, List.append_assoc, List.cons_append, List.nil_append,
        List.singleton_append, List.take_zero, List.drop_zero, List.append_nil]))

theorem Bits.take' {u : List Nat} (hu : Bits u) (n : Nat) : Bits (u.take n) :=
  fun a ha => hu a (List.mem_of_mem_take ha)

theorem Bits.drop' {u : List Nat} (hu : Bits u) (n : Nat) : Bits (u.drop n) :=
  fun a ha => hu a (List.mem_of_mem_drop ha)

/-- The cell of the position after the move right (clamped at the final cell). -/
def mvR (u : List Nat) (p : Nat) : Nat := min (p + 1) u.length

/-- `w = 1, d = 1`: the marker of the current head moves right. -/
theorem actR (Qc Y SL SR u : List Nat) (g p : Nat) (hQ : Bits Qc) (hY : NoB Y) (hS : NoB SL) (hSR : NoB SR)
    (hu : Bits u) (hp : p ≤ u.length) (hSRs : SR = [] ∨ ∃ S, SR = 1 :: S) :
    mhBase.Reach
      (hdR QMH.G211 (Qc ++ List.replicate g 0 ++ [0, 0, 1]) (Y ++ 0 :: cfg u SL p SR))
      (hd Q.RTW Qc (List.replicate g 0 ++ 0 :: rdCell u (mvR u p) :: 1 :: (Y ++ 0 :: cfg u SL (mvR u p) SR))) := by
  by_cases hlt : p < u.length
  · have hm : mvR u p = p + 1 := by unfold mvR; omega
    rw [hm]
    have eD : u.drop p = u[p] :: u.drop (p + 1) := List.drop_eq_getElem_cons hlt
    have eT : u.take (p + 1) = u.take p ++ [u[p]] := take_succ_app u p hlt
    have hb : u[p] ∈ bits := hu _ (List.getElem_mem hlt)
    have hP : NoB (SL ++ 1 :: u.take p) := hS.app (NoB.one_cons _ (hu.take' p))
    have hT : Sym4 (u.drop (p + 1) ++ SR) := (hu.drop' _).sym4.app hSR.sym4
    have h1 := actMR Qc Y (SL ++ 1 :: u.take p) (u.drop (p + 1) ++ SR) g u[p] hb hQ hY hP hT
    have h2 := carrySem Qc Y SL SR u g (p + 1) hQ hY hS hu (by omega) hSRs hSR.sym4
    refine (h1.ofEq ?_ rfl).trans (h2.ofEq ?_ ?_)
    all_goals first
      | exact hdR_eq (by simp only [cfg, uc, eT, eD, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]) (by simp only [cfg, uc, eT, eD, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append])
      | exact hd_eq (by simp only [cfg, uc, eT, eD, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]) (by simp only [cfg, uc, eT, eD, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append])
  · have hpe : p = u.length := by omega
    have hm : mvR u p = p := by unfold mvR; omega
    rw [hm]
    have e1 : rdCell u p = 0 := by simp [rdCell, hpe]
    rw [e1]
    have eD : u.drop p = [] := by rw [hpe]; exact List.drop_length
    have eT : u.take p = u := by rw [hpe]; exact List.take_length
    have hP : NoB (SL ++ 1 :: u) := hS.app (NoB.one_cons _ hu)
    rcases hSRs with rfl | ⟨S, rfl⟩
    · have h1 := actMR0 Qc Y (SL ++ 1 :: u) g hQ hY hP
      have h2 := carryK Qc Y (SL ++ 1 :: u) [0] g hQ hY hP (by intro a ha; simp at ha; subst ha; simp [ALL])
      refine (h1.ofEq ?_ rfl).trans (h2.ofEq rfl ?_)
      all_goals first
        | exact hdR_eq (by simp only [cfg, uc, eT, eD, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]) (by simp only [cfg, uc, eT, eD, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append])
        | exact hd_eq (by simp only [cfg, uc, eT, eD, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]) (by simp only [cfg, uc, eT, eD, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append])
    · have hS4 : Sym4 S := fun a ha => hSR.sym4 a (List.mem_cons_of_mem _ ha)
      have h1 := actMR1 Qc Y (SL ++ 1 :: u) S g hQ hY hP hS4
      have h2 := carryK Qc Y (SL ++ 1 :: u) ([0, 1] ++ S) g hQ hY hP
        (Sym4.app (by intro a ha; simp at ha; rcases ha with rfl | rfl <;> simp [ALL]) hS4)
      refine (h1.ofEq ?_ rfl).trans (h2.ofEq rfl ?_)
      all_goals first
        | exact hdR_eq (by simp only [cfg, uc, eT, eD, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]) (by simp only [cfg, uc, eT, eD, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append])
        | exact hd_eq (by simp only [cfg, uc, eT, eD, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]) (by simp only [cfg, uc, eT, eD, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append])


/-- The position after the move left (clamped at `0`). -/
def mvL (p : Nat) : Nat := p - 1

/-- `w = 1, d = 0`: the marker of the current head moves left. -/
theorem actL (Qc Y SL SR u : List Nat) (g p : Nat) (hQ : Bits Qc) (hY : NoB Y) (hS : NoB SL) (hSR : NoB SR)
    (hu : Bits u) (hp : p ≤ u.length) (hSRs : SR = [] ∨ ∃ S, SR = 1 :: S) :
    mhBase.Reach
      (hdR QMH.G210 (Qc ++ List.replicate g 0 ++ [0, 0, 1]) (Y ++ 0 :: cfg u SL p SR))
      (hd Q.RTW Qc (List.replicate g 0 ++ 0 :: rdCell u (mvL p) :: 1 :: (Y ++ 0 :: cfg u SL (mvL p) SR))) := by
  cases p with
  | zero =>
    have hm : mvL 0 = 0 := rfl
    rw [hm]
    have e1 : rdCell u 0 = 0 := by simp [rdCell]
    rw [e1]
    have hT : Sym4 (u ++ SR) := hu.sym4.app hSR.sym4
    have h1 := actML0 Qc Y SL (u ++ SR) g hQ hY hS hT
    have h2 := carryK Qc Y SL ([1, 0] ++ (u ++ SR)) g hQ hY hS
      (Sym4.app (by intro a ha; simp at ha; rcases ha with rfl | rfl <;> simp [ALL]) hT)
    refine (h1.ofEq ?_ rfl).trans (h2.ofEq rfl ?_)
    closeEq
  | succ q =>
    have hm : mvL (q + 1) = q := rfl
    rw [hm]
    have hlt : q < u.length := by omega
    have eD : u.drop q = u[q] :: u.drop (q + 1) := List.drop_eq_getElem_cons hlt
    have eT : u.take (q + 1) = u.take q ++ [u[q]] := take_succ_app u q hlt
    have hb : u[q] ∈ bits := hu _ (List.getElem_mem hlt)
    have hP : NoB (SL ++ 1 :: u.take q) := hS.app (NoB.one_cons _ (hu.take' q))
    have hT : Sym4 (u.drop (q + 1) ++ SR) := (hu.drop' _).sym4.app hSR.sym4
    have h1 := actML Qc Y (SL ++ 1 :: u.take q) (u.drop (q + 1) ++ SR) g u[q] hb hQ hY hP hT
    have h2 := carrySem Qc Y SL SR u g q hQ hY hS hu (by omega) hSRs hSR.sym4
    refine (h1.ofEq ?_ rfl).trans (h2.ofEq ?_ ?_)
    closeEq

/-- `w = 0, d = 1`: the next head, the unit to the left (the leftmost unit stays). -/
theorem actN (Qc Y SL' SR u : List Nat) (g p p' : Nat) (hQ : Bits Qc) (hY : NoB Y) (hS : NoB SL') (hSR : NoB SR)
    (hu : Bits u) (hp : p ≤ u.length) (hp' : p' ≤ u.length) :
    mhBase.Reach
      (hdR QMH.G201 (Qc ++ List.replicate g 0 ++ [0, 0, 1]) (Y ++ 0 :: cfg u (SL' ++ uc u p' 1) p SR))
      (hd Q.RTW Qc (List.replicate g 0 ++ 0 :: rdCell u p' :: 1 :: (Y ++ 0 :: cfg u SL' p' (uc u p 1 ++ SR)))) := by
  have eD : u.drop p' = u.drop p' := rfl
  have hP : NoB (SL' ++ 1 :: u.take p') := hS.app (NoB.one_cons _ (hu.take' p'))
  have hT : Sym4 (u.drop p ++ SR) := (hu.drop' _).sym4.app hSR.sym4
  have h1 := actLS Qc Y (SL' ++ 1 :: u.take p') (u.drop p') (u.take p) (u.drop p ++ SR) g hQ hY hP
    (hu.drop' _) (hu.take' _) hT
  have hSR' : NoB (uc u p 1 ++ SR) := (NoB.uc hu p).app hSR
  have h2 := carrySem Qc Y SL' (uc u p 1 ++ SR) u g p' hQ hY hS hu hp' (Or.inr ⟨_, rfl⟩) hSR'.sym4
  refine (h1.ofEq ?_ rfl).trans (h2.ofEq ?_ ?_)
  closeEq

/-- `w = 0, d = 1` at the leftmost unit: nothing changes. -/
theorem actN0 (Qc Y SR u : List Nat) (g p : Nat) (hQ : Bits Qc) (hY : NoB Y) (hSR : NoB SR)
    (hu : Bits u) (hp : p ≤ u.length) (hSRs : SR = [] ∨ ∃ S, SR = 1 :: S) :
    mhBase.Reach
      (hdR QMH.G201 (Qc ++ List.replicate g 0 ++ [0, 0, 1]) (Y ++ 0 :: cfg u [] p SR))
      (hd Q.RTW Qc (List.replicate g 0 ++ 0 :: rdCell u p :: 1 :: (Y ++ 0 :: cfg u [] p SR))) := by
  have hT : Sym4 (u.drop p ++ SR) := (hu.drop' _).sym4.app hSR.sym4
  have h1 := actLS0 Qc Y (u.take p) (u.drop p ++ SR) g hQ hY (hu.take' _) hT
  have h2 := carrySem Qc Y [] SR u g p hQ hY NoB.nil hu hp hSRs hSR.sym4
  refine (h1.ofEq ?_ rfl).trans (h2.ofEq ?_ ?_)
  closeEq

/-- `w = 0, d = 0`: the previous head, the unit to the right. -/
theorem actS (Qc Y SL SR u : List Nat) (g p p' : Nat) (hQ : Bits Qc) (hY : NoB Y) (hS : NoB SL) (hSR : NoB SR)
    (hu : Bits u) (hp : p ≤ u.length) (hp' : p' ≤ u.length) (hSRs : SR = [] ∨ ∃ S, SR = 1 :: S) :
    mhBase.Reach
      (hdR QMH.G200 (Qc ++ List.replicate g 0 ++ [0, 0, 1]) (Y ++ 0 :: cfg u SL p (uc u p' 1 ++ SR)))
      (hd Q.RTW Qc (List.replicate g 0 ++ 0 :: rdCell u p' :: 1 :: (Y ++ 0 :: cfg u (SL ++ uc u p 1) p' SR))) := by
  have hT : Sym4 (u.drop p' ++ SR) := (hu.drop' _).sym4.app hSR.sym4
  have h1 := actRS Qc Y SL (u.take p) (u.drop p) (u.take p') (u.drop p' ++ SR) g hQ hY hS (hu.take' _)
    (hu.drop' _) (hu.take' _) hT
  have hS' : NoB (SL ++ uc u p 1) := hS.app (NoB.uc hu p)
  have h2 := carrySem Qc Y (SL ++ uc u p 1) SR u g p' hQ hY hS' hu hp' hSRs hSR.sym4
  refine (h1.ofEq ?_ rfl).trans (h2.ofEq ?_ ?_)
  closeEq

/-- `w = 0, d = 0` at the rightmost unit: nothing changes. -/
theorem actS0 (Qc Y SL u : List Nat) (g p : Nat) (hQ : Bits Qc) (hY : NoB Y) (hS : NoB SL)
    (hu : Bits u) (hp : p ≤ u.length) :
    mhBase.Reach
      (hdR QMH.G200 (Qc ++ List.replicate g 0 ++ [0, 0, 1]) (Y ++ 0 :: cfg u SL p []))
      (hd Q.RTW Qc (List.replicate g 0 ++ 0 :: rdCell u p :: 1 :: (Y ++ 0 :: cfg u SL p []))) := by
  have h1 := actRS0 Qc Y SL (u.take p) (u.drop p) g hQ hY hS (hu.take' _) (hu.drop' _)
  have h2 := carrySem Qc Y SL [] u g p hQ hY hS hu hp (Or.inl rfl) Sym4.nil
  refine (h1.ofEq ?_ rfl).trans (h2.ofEq ?_ ?_)
  closeEq


/-! ## The act on `storeOf` -/

theorem storeOf_decomp (x : List Bool) (pre : List Nat) (p : Nat) (post : List Nat) :
    storeOf x (pre ++ p :: post) pre.length = cfg (uOf x) (ucs (uOf x) post) p (ucs (uOf x) pre) := by
  unfold storeOf
  have e1 : (pre ++ p :: post).drop (pre.length + 1) = post := by
    rw [List.drop_append]; simp
  have e2 : (pre ++ p :: post).take pre.length = pre := by simp
  have e3 : (pre ++ p :: post).getD pre.length 0 = p := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
  rw [e1, e2, e3]

/-- The new head positions and current head after the operation `(w, d)` (as in `runMHAux`). -/
def actPos (n : Nat) (w d : Bool) (pos : List Nat) (cur : Nat) : List Nat :=
  if w then pos.set cur (if d then min (pos.getD cur 0 + 1) (n + 1) else pos.getD cur 0 - 1) else pos

def actCur (np : Nat) (w d : Bool) (cur : Nat) : Nat :=
  if w then cur else if d then min (cur + 1) np else cur - 1

/-- The state `G2 w d`. -/
def g2Of (w d : Bool) : Nat :=
  if w then (if d then QMH.G211 else QMH.G210) else (if d then QMH.G201 else QMH.G200)

theorem getD_le {pos : List Nat} {n : Nat} (h : ∀ p ∈ pos, p ≤ n + 1) (cur : Nat) : pos.getD cur 0 ≤ n + 1 := by
  by_cases hc : cur < pos.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]
    exact h _ (List.getElem_mem hc)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    exact Nat.zero_le _

theorem actPos_bound (n : Nat) (w d : Bool) (pos : List Nat) (cur : Nat) (hpos : ∀ p ∈ pos, p ≤ n + 1) :
    ∀ p ∈ actPos n w d pos cur, p ≤ n + 1 := by
  have hg := getD_le hpos cur
  intro q hq
  cases w
  · simpa [actPos] using hpos q (by simpa [actPos] using hq)
  · simp only [actPos, ite_true] at hq
    rcases List.mem_or_eq_of_mem_set hq with h | h
    · exact hpos q h
    · subst h
      split <;> omega


theorem getD_at (pre : List Nat) (v : Nat) (post : List Nat) : (pre ++ v :: post).getD pre.length 0 = v := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem set_at (pre : List Nat) (p v : Nat) (post : List Nat) :
    (pre ++ p :: post).set pre.length v = pre ++ v :: post := by
  simp [List.set_append_right]

theorem exists_decomp {pos : List Nat} {cur : Nat} (h : cur < pos.length) :
    ∃ pre p post, pos = pre ++ p :: post ∧ cur = pre.length := by
  refine ⟨pos.take cur, pos[cur], pos.drop (cur + 1), ?_, by simp; omega⟩
  rw [← List.drop_eq_getElem_cons h, List.take_append_drop]

/-- The act, with the new head positions given by a decomposition. -/
theorem actD (w d : Bool) (x : List Bool) (pre : List Nat) (p : Nat) (post : List Nat)
    (hpos : ∀ q ∈ pre ++ p :: post, q ≤ x.length + 1) (Qc Y : List Nat) (g : Nat) (hQ : Bits Qc) (hY : NoB Y) :
    ∃ pre' p' post', actPos x.length w d (pre ++ p :: post) pre.length = pre' ++ p' :: post' ∧
      actCur ((pre ++ p :: post).length - 1) w d pre.length = pre'.length ∧
      p' ≤ x.length + 1 ∧
      mhBase.Reach
        (hdR (g2Of w d) (Qc ++ List.replicate g 0 ++ [0, 0, 1])
          (Y ++ 0 :: cfg (uOf x) (ucs (uOf x) post) p (ucs (uOf x) pre)))
        (hd Q.RTW Qc (List.replicate g 0 ++ 0 :: rdCell (uOf x) p' :: 1 ::
          (Y ++ 0 :: cfg (uOf x) (ucs (uOf x) post') p' (ucs (uOf x) pre')))) := by
  have hu := Bits.uOf x
  have hlen := length_uOf x
  have hp : p ≤ x.length + 1 := hpos p (List.mem_append_right _ (List.mem_cons_self ..))
  have hpre : ∀ q ∈ pre, q ≤ x.length + 1 := fun q hq => hpos q (List.mem_append_left _ hq)
  have hpost : ∀ q ∈ post, q ≤ x.length + 1 :=
    fun q hq => hpos q (List.mem_append_right _ (List.mem_cons_of_mem _ hq))
  have hSL := NoB.ucs hu post
  have hSR := NoB.ucs hu pre
  have hp' : p ≤ (uOf x).length := by omega
  cases w
  · cases d
    · -- previous head: the unit to the right
      rcases List.eq_nil_or_concat pre with rfl | ⟨pre', p', rfl⟩
      · refine ⟨[], p, post, by simp [actPos], by simp [actCur], hp, ?_⟩
        simpa [g2Of] using actS0 Qc Y (ucs (uOf x) post) (uOf x) g p hQ hY hSL hu hp'
      · simp only [List.concat_eq_append] at hpos hpre ⊢
        have hq' : p' ≤ x.length + 1 := hpre p' (by simp)
        refine ⟨pre', p', p :: post, by simp [actPos], by simp [actCur], hq', ?_⟩
        have h := actS Qc Y (ucs (uOf x) post) (ucs (uOf x) pre') (uOf x) g p p' hQ hY hSL
          (NoB.ucs hu pre') hu hp' (by omega) (ucs_shape _ _)
        simp only [ucs_snoc, ucs_cons]
        simpa [g2Of] using h
    · -- next head: the unit to the left
      rcases post with _ | ⟨p', post'⟩
      · refine ⟨pre, p, [], by simp [actPos], by simp [actCur], hp, ?_⟩
        simpa [g2Of] using actN0 Qc Y (ucs (uOf x) pre) (uOf x) g p hQ hY hSR hu hp' (ucs_shape _ _)
      · have hq' : p' ≤ x.length + 1 := hpost p' (by simp)
        refine ⟨pre ++ [p], p', post', by simp [actPos], by simp [actCur], hq', ?_⟩
        have h := actN Qc Y (ucs (uOf x) post') (ucs (uOf x) pre) (uOf x) g p p' hQ hY
          (NoB.ucs hu post') hSR hu hp' (by omega)
        simp only [ucs_snoc, ucs_cons]
        simpa [g2Of] using h
  · -- w = 1: move the marker
    cases d
    · have h := actL Qc Y (ucs (uOf x) post) (ucs (uOf x) pre) (uOf x) g p hQ hY hSL hSR hu hp' (ucs_shape _ _)
      refine ⟨pre, mvL p, post, ?_, by simp [actCur], by unfold mvL; omega, by simpa [g2Of] using h⟩
      simp [actPos, set_at, getD_at, mvL]
    · have h := actR Qc Y (ucs (uOf x) post) (ucs (uOf x) pre) (uOf x) g p hQ hY hSL hSR hu hp' (ucs_shape _ _)
      refine ⟨pre, mvR (uOf x) p, post, ?_, by simp [actCur], by unfold mvR; omega, by simpa [g2Of] using h⟩
      simp [actPos, set_at, getD_at, mvR, hlen]

/-- **The act.** From `G2 w d` right of `H` (blank `c`) to `RTW`: the storage of `storeOf x pos cur` becomes the
storage of the head positions after the operation `(w, d)` of `runMHAux`, and the scanned symbol of the new current head
is written into `c`. The head positions stay `≤ |x| + 1`. -/
theorem act (w d : Bool) (x : List Bool) (pos : List Nat) (cur : Nat) (hcur : cur < pos.length)
    (hpos : ∀ p ∈ pos, p ≤ x.length + 1) (Qc Y : List Nat) (g : Nat) (hQ : Bits Qc) (hY : NoB Y) :
    mhBase.Reach
      (hdR (g2Of w d) (Qc ++ List.replicate g 0 ++ [0, 0, 1]) (Y ++ 0 :: storeOf x pos cur))
      (hd Q.RTW Qc (List.replicate g 0 ++ 0 ::
        cellN (mhRead x ((actPos x.length w d pos cur).getD (actCur (pos.length - 1) w d cur) 0)) :: 1 ::
        (Y ++ 0 :: storeOf x (actPos x.length w d pos cur) (actCur (pos.length - 1) w d cur)))) := by
  obtain ⟨pre, p, post, rfl, rfl⟩ := exists_decomp hcur
  obtain ⟨pre', p', post', e1, e2, hp', h⟩ := actD w d x pre p post hpos Qc Y g hQ hY
  rw [e1, e2, getD_at, cellN_mhRead x p' hp', storeOf_decomp x pre p post, storeOf_decomp x pre' p' post']
  exact h

end ZP.MH
