module

public import ZP.Defs
public import ZP.Logic
public import ZP.SymExec
public import ZP.Outer

@[expose] public section

/-!
# Layer N3: the rotation of the guest code

The interpreter keeps the cyclic code `R` as `Q = reverse R` left of its work area.
A rotation moves bits one at a time from `Q`'s right end (`R`'s front) to `Q`'s left
end: `w`, `d`, the run of 1s, then the closing 0. Each move is one `rotl1`. This file
proves that `rot` (`ZP/Defs.lean`) is `rotl (entryOnes R + 3)`, and that the machine
performs exactly those moves (normal mode `TW`/`TD`/`TO`, recording mode
`RTW`/`RTD`/`RTO`).
-/

namespace ZP

/-! ## Rotations of lists -/

def rotl1 {α : Type} (R : List α) : List α := R.drop 1 ++ R.take 1

def rotl {α : Type} : Nat → List α → List α
  | 0, R => R
  | j + 1, R => rotl j (rotl1 R)

theorem rotl_add {α : Type} (a : Nat) : ∀ (b : Nat) (R : List α), rotl (a + b) R = rotl a (rotl b R)
  | 0, _ => rfl
  | b + 1, R => by
    show rotl (a + b) (rotl1 R) = rotl a (rotl b (rotl1 R))
    exact rotl_add a b (rotl1 R)

theorem rotl1_cons {α : Type} (a : α) (T : List α) : rotl1 (a :: T) = T ++ [a] := by
  simp [rotl1]

theorem rotl_split {α : Type} : ∀ (A B : List α), rotl A.length (A ++ B) = B ++ A
  | [], B => by simp [rotl]
  | a :: A, B => by
    show rotl A.length (rotl1 (a :: (A ++ B))) = B ++ a :: A
    rw [rotl1_cons, List.append_assoc, rotl_split A (B ++ [a])]
    simp

theorem rotl_length {α : Type} (R : List α) : rotl R.length R = R := by
  have := rotl_split R []
  simpa using this

theorem rotl_mul {α : Type} (R : List α) : ∀ q : Nat, rotl (R.length * q) R = R
  | 0 => rfl
  | q + 1 => by
    rw [show R.length * (q + 1) = R.length * q + R.length from Nat.mul_succ _ _, rotl_add,
      rotl_length, rotl_mul R q]

theorem rotl_nil {α : Type} : ∀ j : Nat, rotl j ([] : List α) = []
  | 0 => rfl
  | j + 1 => by
    show rotl j (rotl1 []) = []
    have e : rotl1 ([] : List α) = [] := rfl
    rw [e, rotl_nil j]

theorem rotl_mod {α : Type} (K : Nat) (R : List α) :
    rotl K R = R.drop (K % R.length) ++ R.take (K % R.length) := by
  cases R with
  | nil => simp [rotl_nil]
  | cons a T =>
    have hpos : 0 < (a :: T).length := Nat.succ_pos _
    have hr : K % (a :: T).length < (a :: T).length := Nat.mod_lt _ hpos
    have hk := Nat.mod_add_div K (a :: T).length
    have h1 : rotl K (a :: T) =
        rotl (K % (a :: T).length) (rotl ((a :: T).length * (K / (a :: T).length)) (a :: T)) := by
      rw [← rotl_add, hk]
    rw [h1, rotl_mul]
    have hl : ((a :: T).take (K % (a :: T).length)).length = K % (a :: T).length := by
      rw [List.length_take]
      omega
    have := rotl_split ((a :: T).take (K % (a :: T).length)) ((a :: T).drop (K % (a :: T).length))
    rw [hl, List.take_append_drop] at this
    exact this

/-- `rot` is `entryOnes R + 3` single moves. -/
theorem rot_eq (R : List Bool) : rot R = rotl (entryOnes R + 3) R := by
  rw [rotl_mod]
  rfl

/-! ## The entry's one-count after the first two moves -/

theorem cyc_rotl1 (a : Bool) (T : List Bool) (i : Nat) :
    cyc (rotl1 (a :: T)) i = cyc (a :: T) (i + 1) := by
  rw [rotl1_cons]
  unfold cyc
  have hn : (T ++ [a]).length = T.length + 1 := by simp
  rw [hn]
  show (T ++ [a]).getD (i % (T.length + 1)) false = (a :: T).getD ((i + 1) % (T.length + 1)) false
  have hr : i % (T.length + 1) < T.length + 1 := Nat.mod_lt i (by omega)
  have hd := Nat.mod_add_div i (T.length + 1)
  by_cases h : i % (T.length + 1) < T.length
  · have e2 : (i + 1) % (T.length + 1) = i % (T.length + 1) + 1 := by
      have e3 : i + 1 = (i % (T.length + 1) + 1) + (T.length + 1) * (i / (T.length + 1)) := by
        omega
      rw [e3, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (show i % (T.length + 1) + 1 < T.length + 1 by omega)]
    rw [e2]
    generalize i % (T.length + 1) = r at h ⊢
    simp [List.getD, List.getElem?_append_left h]
  · have h' : i % (T.length + 1) = T.length := by omega
    have e2 : (i + 1) % (T.length + 1) = 0 := by
      have e3 : i + 1 = (T.length + 1) * (i / (T.length + 1) + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      rw [e3, Nat.mul_mod_right]
    rw [e2, h']
    simp [List.getD]

theorem cyc_rotl1' {R : List Bool} (h : R ≠ []) (i : Nat) : cyc (rotl1 R) i = cyc R (i + 1) := by
  cases R with
  | nil => exact absurd rfl h
  | cons a T => exact cyc_rotl1 a T i

theorem rotl1_ne_nil {R : List Bool} (h : R ≠ []) : rotl1 R ≠ [] := by
  cases R with
  | nil => exact absurd rfl h
  | cons a T => rw [rotl1_cons]; simp

theorem length_rotl1 {α : Type} (R : List α) : (rotl1 R).length = R.length := by
  cases R with
  | nil => rfl
  | cons a T => rw [rotl1_cons]; simp

theorem onesFrom_shift {R Y : List Bool} {s : Nat} (hc : ∀ j, cyc R (j + s) = cyc Y j) :
    ∀ f j, onesFrom R f (j + s) = onesFrom Y f j
  | 0, _ => rfl
  | f + 1, j => by
    show (if cyc R (j + s) = true then onesFrom R f (j + s + 1) + 1 else 0) =
      (if cyc Y j = true then onesFrom Y f (j + 1) + 1 else 0)
    rw [hc, show j + s + 1 = (j + 1) + s by omega, onesFrom_shift hc f (j + 1)]

theorem cyc_ones (m : Nat) (R' : List Bool) (i : Nat) (hi : i < m) :
    cyc (List.replicate m true ++ false :: R') i = true := by
  unfold cyc
  have hl : (List.replicate m true ++ false :: R').length = m + 1 + R'.length := by
    simp only [List.length_append, List.length_replicate, List.length_cons]; omega
  rw [hl, Nat.mod_eq_of_lt (show i < m + 1 + R'.length by omega)]
  have hi' : i < (List.replicate m true).length := by simpa using hi
  simp [List.getD, List.getElem?_append_left hi', hi]

theorem cyc_zero (m : Nat) (R' : List Bool) :
    cyc (List.replicate m true ++ false :: R') m = false := by
  unfold cyc
  have hl : (List.replicate m true ++ false :: R').length = m + 1 + R'.length := by
    simp only [List.length_append, List.length_replicate, List.length_cons]; omega
  rw [hl, Nat.mod_eq_of_lt (show m < m + 1 + R'.length by omega)]
  simp [List.getD]

theorem onesFrom_ones (m : Nat) (R' : List Bool) :
    ∀ f i, i ≤ m → m - i < f → onesFrom (List.replicate m true ++ false :: R') f i = m - i
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, i, hi, h => by
    show (if cyc (List.replicate m true ++ false :: R') i = true then
        onesFrom (List.replicate m true ++ false :: R') f (i + 1) + 1 else 0) = m - i
    by_cases him : i < m
    · rw [cyc_ones m R' i him, if_pos rfl, onesFrom_ones m R' f (i + 1) (by omega) (by omega)]
      omega
    · have e : i = m := by omega
      subst e
      rw [cyc_zero, if_neg Bool.false_ne_true]
      omega

theorem split0 : ∀ Y : List Bool, false ∈ Y → ∃ m R', Y = List.replicate m true ++ false :: R'
  | [], h => by simp at h
  | false :: Y, _ => ⟨0, Y, rfl⟩
  | true :: Y, h => by
    have h' : false ∈ Y := by simpa using h
    obtain ⟨m, R', e⟩ := split0 Y h'
    exact ⟨m + 1, R', by rw [e]; rfl⟩

theorem mem_rotl1 {a : Bool} {R : List Bool} (h : a ∈ R) : a ∈ rotl1 R := by
  cases R with
  | nil => simp at h
  | cons b T =>
    rw [rotl1_cons]
    rcases List.mem_cons.mp h with e | e
    · rw [e]; exact List.mem_append_right _ (List.mem_cons_self ..)
    · exact List.mem_append_left _ e

/-- After the moves of `w` and `d`, `R` reads `1^m 0 R'` with `m = entryOnes`. -/
theorem entry_split (R : List Bool) (h0 : false ∈ R) :
    ∃ m R', rotl 2 R = List.replicate m true ++ false :: R' ∧ entryOnes R = m ∧
      rot R = R' ++ (List.replicate m true ++ [false]) := by
  have hne : R ≠ [] := by intro e; rw [e] at h0; simp at h0
  have hne1 : rotl1 R ≠ [] := rotl1_ne_nil hne
  have hmem : false ∈ rotl 2 R := mem_rotl1 (mem_rotl1 h0)
  obtain ⟨m, R', e⟩ := split0 (rotl 2 R) hmem
  have hc : ∀ j, cyc R (j + 2) = cyc (rotl 2 R) j := by
    intro j
    show cyc R (j + 2) = cyc (rotl1 (rotl1 R)) j
    rw [cyc_rotl1' hne1, cyc_rotl1' hne]
    all_goals rfl
  have hlen : (rotl 2 R).length = R.length := by
    show (rotl1 (rotl1 R)).length = R.length
    rw [length_rotl1, length_rotl1]
  have hent : entryOnes R = m := by
    show onesFrom R R.length 2 = m
    have := onesFrom_shift hc R.length 0
    rw [Nat.zero_add] at this
    rw [this, e]
    have hl : R.length = m + 1 + R'.length := by
      rw [← hlen, e]
      simp only [List.length_append, List.length_replicate, List.length_cons]; omega
    rw [onesFrom_ones m R' R.length 0 (Nat.zero_le _) (by omega)]
    omega
  refine ⟨m, R', e, hent, ?_⟩
  rw [rot_eq, hent, show m + 3 = (m + 1) + 2 by omega, rotl_add, e]
  have := rotl_split (List.replicate m true ++ [false]) R'
  have hA : (List.replicate m true ++ [false]).length = m + 1 := by simp
  rw [hA, List.append_assoc] at this
  exact this

/-! ## The machine: one move -/

def ALL : List Nat := [0, 1, 2, 3]

def Bits (w : List Nat) : Prop := ∀ a ∈ w, a ∈ bits

theorem Bits.cons {b : Nat} {w : List Nat} (hb : b ∈ bits) (hw : Bits w) : Bits (b :: w) := by
  intro a ha
  rcases List.mem_cons.mp ha with e | e
  · rw [e]; exact hb
  · exact hw a e

theorem Bits.snoc {b : Nat} {w : List Nat} (hw : Bits w) (hb : b ∈ bits) : Bits (w ++ [b]) := by
  intro a ha
  rcases List.mem_append.mp ha with e | e
  · exact hw a e
  · rw [List.mem_singleton.mp e]; exact hb

theorem Bits.app {u v : List Nat} (hu : Bits u) (hv : Bits v) : Bits (u ++ v) := by
  intro a ha
  rcases List.mem_append.mp ha with e | e
  · exact hu a e
  · exact hv a e

theorem Bits.tail {b : Nat} {w : List Nat} (h : Bits (b :: w)) : Bits w :=
  fun a ha => h a (List.mem_cons_of_mem _ ha)

theorem Bits.head {b : Nat} {w : List Nat} (h : Bits (b :: w)) : b ∈ bits :=
  h b (List.mem_cons_self ..)

theorem Bits.ofB (w : List Bool) : Bits (bitsOf w) := bitsOf_bits w

/-- Rotating: head on `Q`'s right end (`R`'s front), holes `H` (shown as `h`) right of
`Q`, then the context `X`. -/
def Fr (q h : Nat) : SC := ⟨q, [.blk 0 .id], [.blk 1 (.const h), .blk 2 .id], true⟩

def Fs (q h b : Nat) : SC := ⟨q, [.sym b, .blk 0 .id], [.blk 1 (.const h), .blk 2 .id], true⟩

/-- After the closing 0: `NAV` right of the 0 just written at `Q`'s left end. -/
def Nv (h : Nat) : SC :=
  ⟨Q.NAV, [.sym 2], [.blk 0 .id, .sym 0, .blk 1 (.const h), .blk 2 .id], false⟩

def rst (q h : Nat) (R H X : List Nat) : ZC := (Fr q h).den [R.reverse, H, X]

/-- `NAV` after a rotation whose result is `R ++ [0]`. -/
def rnav (h : Nat) (R H X : List Nat) : ZC := (Nv h).den [R.reverse, H, X]

theorem rst_cons (q h b : Nat) (R H X : List Nat) :
    rst q h (b :: R) H X = (Fs q h b).den [R.reverse, H, X] := by
  have e : dL [(b :: R).reverse, H, X] [.blk 0 .id] = dL [R.reverse, H, X] [.sym b, .blk 0 .id] := by
    show ((b :: R).reverse.map Fn.id.app).reverse ++ [] =
      [b].reverse ++ ((R.reverse.map Fn.id.app).reverse ++ [])
    rw [map_id_app, map_id_app]
    simp
  show (⟨q, stail (sapp (dL [(b :: R).reverse, H, X] [.blk 0 .id]) blank),
      scons (sapp (dL [(b :: R).reverse, H, X] [.blk 0 .id]) blank 0)
        (sapp (dR [(b :: R).reverse, H, X] [.blk 1 (.const h), .blk 2 .id]) blank)⟩ : ZC) =
    ⟨q, stail (sapp (dL [R.reverse, H, X] [.sym b, .blk 0 .id]) blank),
      scons (sapp (dL [R.reverse, H, X] [.sym b, .blk 0 .id]) blank 0)
        (sapp (dR [R.reverse, H, X] [.blk 1 (.const h), .blk 2 .id]) blank)⟩
  rw [e]
  rfl

def rsets : Env := [bits, bits, ALL]

theorem rvalid {R H X : List Nat} (hR : Bits R) (hH : Bits H) (hX : ∀ a ∈ X, a ∈ ALL) :
    Valid rsets [R.reverse, H, X] :=
  Valid.cons (fun a ha => hR a (List.mem_reverse.mp ha)) (Valid.cons hH (Valid.cons hX (Valid.nil _)))

/-- One move, from a symbolic check. -/
theorem rstep {q q' h b k : Nat} {R H X : List Nat} (hR : Bits R) (hH : Bits H)
    (hX : ∀ a ∈ X, a ∈ ALL)
    (hc : mreachN zpLogic rsets [] k ((Fs q h b).norm [])
      ((Fr q' h).subst (Item.inst [[.sym b, .blk 0 .id], [.sym b, .blk 1 .id], [.blk 2 .id]])) = true) :
    zpLogic.Reach (rst q h (b :: R) H X) (rst q' h (R ++ [b]) (b :: H) X) := by
  rw [rst_cons]
  have := checkI (E := []) (rvalid hR hH hX) trivial hc
  have e : (R ++ [b]).reverse = b :: R.reverse := by simp
  unfold rst
  rw [e]
  exact this

/-- The closing 0. -/
theorem rfin {q h k : Nat} {R H X : List Nat} (hR : Bits R) (hH : Bits H) (hX : ∀ a ∈ X, a ∈ ALL)
    (hc : mreachN zpLogic rsets [] k ((Fs q h 2).norm [])
      ((Nv h).subst (Item.inst [[.blk 0 .id], [.blk 1 .id], [.blk 2 .id]])) = true) :
    zpLogic.Reach (rst q h (2 :: R) H X) (rnav h R H X) := by
  rw [rst_cons]
  exact checkI (E := []) (rvalid hR hH hX) trivial hc

/-! ## The moves of a whole rotation -/

def ones (m : Nat) : List Nat := List.replicate m 3

theorem Bits.rep (m : Nat) : Bits (ones m) := by
  intro a ha
  rw [List.eq_of_mem_replicate ha]
  simp [bits]

theorem ones_snoc (m : Nat) : ones m ++ [3] = 3 :: ones m := by
  show List.replicate m 3 ++ [3] = List.replicate (m + 1) 3
  rw [List.replicate_succ']

/-- Moving step lemmas, for one mode. -/
structure RotMode (qW qD qO h : Nat) : Prop where
  w : ∀ b R H X, b ∈ bits → Bits R → Bits H → (∀ a ∈ X, a ∈ ALL) →
    zpLogic.Reach (rst qW h (b :: R) H X) (rst qD h (R ++ [b]) (b :: H) X)
  d : ∀ b R H X, b ∈ bits → Bits R → Bits H → (∀ a ∈ X, a ∈ ALL) →
    zpLogic.Reach (rst qD h (b :: R) H X) (rst qO h (R ++ [b]) (b :: H) X)
  o : ∀ R H X, Bits R → Bits H → (∀ a ∈ X, a ∈ ALL) →
    zpLogic.Reach (rst qO h (3 :: R) H X) (rst qO h (R ++ [3]) (3 :: H) X)
  z : ∀ R H X, Bits R → Bits H → (∀ a ∈ X, a ∈ ALL) →
    zpLogic.Reach (rst qO h (2 :: R) H X) (rnav h R H X)

theorem oloop {qW qD qO h : Nat} (M : RotMode qW qD qO h) :
    ∀ m R H X, Bits R → Bits H → (∀ a ∈ X, a ∈ ALL) →
      zpLogic.Reach (rst qO h (ones m ++ 2 :: R) H X) (rnav h (R ++ ones m) (ones m ++ H) X)
  | 0, R, H, X, hR, hH, hX => by
    show zpLogic.Reach (rst qO h (2 :: R) H X) (rnav h (R ++ []) H X)
    rw [List.append_nil]
    exact M.z R H X hR hH hX
  | m + 1, R, H, X, hR, hH, hX => by
    show zpLogic.Reach (rst qO h (3 :: (ones m ++ 2 :: R)) H X)
      (rnav h (R ++ 3 :: ones m) ((3 :: ones m) ++ H) X)
    refine (M.o _ H X ((Bits.rep m).app (Bits.cons (by simp [bits]) hR)) hH hX).trans ?_
    have e1 : ones m ++ 2 :: R ++ [3] = ones m ++ 2 :: (R ++ [3]) := by simp
    have e2 : R ++ 3 :: ones m = (R ++ [3]) ++ ones m := by simp
    have e3 : (3 :: ones m) ++ H = ones m ++ 3 :: H := by
      rw [← ones_snoc, List.append_assoc, List.singleton_append]
    rw [e1, e2, e3]
    exact oloop M m (R ++ [3]) (3 :: H) X (hR.snoc (by simp [bits]))
      (Bits.cons (by simp [bits]) hH) hX

theorem bitsOf_snoc (w : List Bool) (b : Bool) :
    bitsOf (w ++ [b]) = bitsOf w ++ [if b then 3 else 2] := by
  simp [bitsOf]

/-- A whole rotation: from `R` (containing a 0) to `rot R`, leaving `entryOnes R + 2`
holes beside the closing 0's hole. -/
theorem rotate {qW qD qO h : Nat} (M : RotMode qW qD qO h) (R : List Bool) (h0 : false ∈ R)
    (X : List Nat) (hX : ∀ a ∈ X, a ∈ ALL) :
    ∃ R' H, bitsOf (rot R) = R' ++ [2] ∧ H.length = entryOnes R + 2 ∧ Bits H ∧
      zpLogic.Reach (rst qW h (bitsOf R) [] X) (rnav h R' H X) := by
  obtain ⟨m, R', e, hent, hrot⟩ := entry_split R h0
  cases R with
  | nil => simp at h0
  | cons a T =>
    have hW := M.w (if a then 3 else 2) (bitsOf T) [] X (Bits.ofB [a] _ (by simp [bitsOf]))
      (Bits.ofB T) (fun _ h => by cases h) hX
    have hR1 : T ++ [a] ≠ [] := by simp
    cases hT : T ++ [a] with
    | nil => exact absurd hT hR1
    | cons c T' =>
      have hTb : bitsOf T ++ [if a then 3 else 2] = (if c then 3 else 2) :: bitsOf T' := by
        rw [← bitsOf_snoc, hT]
        rfl
      have hD := M.d (if c then 3 else 2) (bitsOf T') [if a then 3 else 2] X
        (Bits.ofB [c] _ (by simp [bitsOf])) (Bits.ofB T')
        (Bits.ofB [a]) hX
      have e2 : rotl 2 (a :: T) = T' ++ [c] := by
        show rotl1 (rotl1 (a :: T)) = T' ++ [c]
        rw [rotl1_cons, hT, rotl1_cons]
      rw [e2] at e
      have hTc : bitsOf T' ++ [if c then 3 else 2] = ones m ++ 2 :: bitsOf R' := by
        rw [← bitsOf_snoc, e]
        simp [bitsOf, ones]
      have hO := oloop M m (bitsOf R') [if c then 3 else 2, if a then 3 else 2] X
        (Bits.ofB R') (Bits.ofB [c, a]) hX
      refine ⟨bitsOf R' ++ ones m, ones m ++ [if c then 3 else 2, if a then 3 else 2], ?_, ?_,
        (Bits.rep m).app (Bits.ofB [c, a]), ?_⟩
      · rw [hrot]
        simp [bitsOf, ones]
      · simp [ones, hent]
      · show zpLogic.Reach (rst qW h ((if a then 3 else 2) :: bitsOf T) [] X) _
        refine hW.trans ?_
        rw [hTb]
        refine hD.trans ?_
        rw [hTc]
        exact hO

/-! ## The two modes -/

theorem rotNormal : RotMode Q.TW Q.TD Q.TO 0 where
  w := by
    intro b R H X hb hR hH hX
    rcases mem_bits hb with rfl | rfl
    · exact rstep (k := 8) hR hH hX (by decide +kernel)
    · exact rstep (k := 8) hR hH hX (by decide +kernel)
  d := by
    intro b R H X hb hR hH hX
    rcases mem_bits hb with rfl | rfl
    · exact rstep (k := 8) hR hH hX (by decide +kernel)
    · exact rstep (k := 8) hR hH hX (by decide +kernel)
  o := fun _ _ _ hR hH hX => rstep (k := 8) hR hH hX (by decide +kernel)
  z := fun _ _ _ hR hH hX => rfin (k := 6) hR hH hX (by decide +kernel)

theorem rotRecord : RotMode Q.RTW Q.RTD Q.RTO 1 where
  w := by
    intro b R H X hb hR hH hX
    rcases mem_bits hb with rfl | rfl
    · exact rstep (k := 8) hR hH hX (by decide +kernel)
    · exact rstep (k := 8) hR hH hX (by decide +kernel)
  d := by
    intro b R H X hb hR hH hX
    rcases mem_bits hb with rfl | rfl
    · exact rstep (k := 8) hR hH hX (by decide +kernel)
    · exact rstep (k := 8) hR hH hX (by decide +kernel)
  o := fun _ _ _ hR hH hX => rstep (k := 8) hR hH hX (by decide +kernel)
  z := fun _ _ _ hR hH hX => rfin (k := 6) hR hH hX (by decide +kernel)

end ZP
