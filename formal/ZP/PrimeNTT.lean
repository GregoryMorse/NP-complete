module

public import ZP.RulerNTT
public import ZP.CheckG
public import ZP.AbstractNTT

@[expose] public section

/-! # NTT machine: the primality test (part 1): copying `P` into `D` -/

namespace ZP.NTT

open ZP ZP.G

theorem repSet (k c : Nat) : ∀ x ∈ List.replicate k c, x ∈ [c] := by
  intro x hx; simp [List.mem_replicate] at hx; simp [hx]

/-- `DC1`: skip the marked cells of `P`, mark the next one, turn back. -/
theorem dc1Mark (A : List Nat) (m : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.DC1 A (List.replicate m 2 ++ 3 :: R))
      (hd QNTT.DC2 (A ++ List.replicate m 2) (2 :: R)) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate m 2, R] :=
    Valid.cons hA (Valid.cons (repSet m 2) (Valid.cons hR (Valid.nil _)))
  exact checkFT (env := [A, List.replicate m 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 3, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.sym 2, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem dc2Scan (L R : List Nat) (hL : NoB L) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.DC2 L R) (hdR QNTT.DC3 [3] (L ++ R)) := by
  have hV : Valid [NB, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [L, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id])
    (ls' := [.sym 3]) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem dc3Walk (d : Nat) (X : List Nat) (hX : Sym4 X) :
    znttLogic.Reach (hdR QNTT.DC3 [3] (List.replicate d 3 ++ 1 :: X))
      (hdR QNTT.DC1 (3 :: List.replicate d 3 ++ [1]) X) := by
  have hV : Valid [[3], ALL] [List.replicate d 3, X] :=
    Valid.cons (repSet d 3) (Valid.cons hX (Valid.nil _))
  exact checkFF (env := [List.replicate d 3, X]) (E := []) (k := 4) hV trivial
    (ls := [.sym 3]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id])
    (ls' := [.sym 3, .blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem dcCycle (d m : Nat) (R : List Nat) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.DC1 (List.replicate d 3 ++ [1]) (List.replicate m 2 ++ 3 :: R))
      (hdR QNTT.DC1 (List.replicate (d + 1) 3 ++ [1]) (List.replicate (m + 1) 2 ++ R)) := by
  have sA : Sym4 (List.replicate d 3 ++ [1]) :=
    (Sym4.rep d 3 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) Sym4.nil)
  have h1 := dc1Mark _ m R sA hR
  have nL : NoB (List.replicate d 3 ++ [1] ++ List.replicate m 2) := by
    simp only [NoB_app_iff, NoB_cons_iff, NoB_rep_iff, NoB_nil_iff]; simp [NB]
  have h2 := dc2Scan _ (2 :: R) nL (Sym4.cons (by simp [ALL]) hR)
  have h3 := dc3Walk d (List.replicate m 2 ++ 2 :: R)
    ((Sym4.rep m 2 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hR))
  simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] at h1 h2 h3
  have e2 : List.replicate (m + 1) 2 ++ R = List.replicate m 2 ++ 2 :: R := by
    simp [List.replicate_succ']
  have e1 : List.replicate (d + 1) 3 ++ [1] = 3 :: (List.replicate d 3 ++ [1]) := by
    simp [List.replicate_succ]
  rw [e1, e2]
  exact h1.trans (h2.trans h3)

theorem dcLoop (rest : List Nat) (hr : Sym4 rest) :
    ∀ (k d m : Nat),
    znttLogic.Reach
      (hdR QNTT.DC1 (List.replicate d 3 ++ [1]) (List.replicate m 2 ++ List.replicate k 3 ++ 1 :: rest))
      (hdR QNTT.DC1 (List.replicate (d + k) 3 ++ [1]) (List.replicate (m + k) 2 ++ 1 :: rest)) := by
  intro k
  induction k with
  | zero => intro d m; simpa using LTM.Reach.refl znttLogic _
  | succ k ih =>
    intro d m
    have h1 := dcCycle d m (List.replicate k 3 ++ 1 :: rest)
      ((Sym4.rep k 3 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hr))
    have h2 := ih (d + 1) (m + 1)
    have e1 : List.replicate m 2 ++ List.replicate (k + 1) 3 ++ 1 :: rest =
        List.replicate m 2 ++ 3 :: (List.replicate k 3 ++ 1 :: rest) := by
      simp [List.replicate_succ]
    rw [e1]
    have := h1.trans (h2.of_eq (by simp [List.append_assoc]) rfl)
    have e2 : d + 1 + k = d + (k + 1) := by omega
    have e3 : m + 1 + k = m + (k + 1) := by omega
    rw [e2, e3] at this
    exact this

/-- `P` exhausted: `DC1` hits `M`, `DCU` unmarks `P`, crosses the separator. -/
theorem dcEnd (d m : Nat) (rest : List Nat) (hr : Sym4 rest) :
    znttLogic.Reach (hdR QNTT.DC1 (List.replicate d 3 ++ [1]) (List.replicate m 2 ++ 1 :: rest))
      (hd QNTT.XS1 (List.replicate d 3) (1 :: (List.replicate m 3 ++ 1 :: rest))) := by
  have sA : Sym4 (List.replicate d 3 ++ [1]) :=
    (Sym4.rep d 3 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) Sym4.nil)
  have sD : Sym4 (List.replicate d 3) := Sym4.rep d 3 (by simp [ALL])
  have hV : Valid [ALL, [2], ALL] [List.replicate d 3 ++ [1], List.replicate m 2, rest] :=
    Valid.cons sA (Valid.cons (repSet m 2) (Valid.cons hr (Valid.nil _)))
  have h1 : znttLogic.Reach (hdR QNTT.DC1 (List.replicate d 3 ++ [1]) (List.replicate m 2 ++ 1 :: rest))
      (hd QNTT.DCU (List.replicate d 3 ++ [1] ++ List.replicate m 2) (1 :: rest)) :=
    checkFT (env := [List.replicate d 3 ++ [1], List.replicate m 2, rest]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
      (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.sym 1, .blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  have hV2 : Valid [ALL, [2], ALL] [List.replicate d 3 ++ [1], List.replicate m 2, 1 :: rest] :=
    Valid.cons sA (Valid.cons (repSet m 2) (Valid.cons (Sym4.cons (by simp [ALL]) hr) (Valid.nil _)))
  have h2 : znttLogic.Reach (hd QNTT.DCU (List.replicate d 3 ++ [1] ++ List.replicate m 2) (1 :: rest))
      (hd QNTT.DCU (List.replicate d 3 ++ [1]) (List.replicate m 3 ++ 1 :: rest)) :=
    checkTT (env := [List.replicate d 3 ++ [1], List.replicate m 2, 1 :: rest]) (E := []) (k := 4) hV2 trivial
      (ls := [.blk 0 .id, .blk 1 .id]) (rs := [.blk 2 .id])
      (ls' := [.blk 0 .id]) (rs' := [.blk 1 (.const 3), .blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  have hV3 : Valid [ALL, ALL] [List.replicate d 3, List.replicate m 3 ++ 1 :: rest] :=
    Valid.cons sD (Valid.cons ((Sym4.rep m 3 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hr)) (Valid.nil _))
  have h3 : znttLogic.Reach (hd QNTT.DCU (List.replicate d 3 ++ [1]) (List.replicate m 3 ++ 1 :: rest))
      (hd QNTT.XS1 (List.replicate d 3) (1 :: (List.replicate m 3 ++ 1 :: rest))) :=
    checkTT (env := [List.replicate d 3, List.replicate m 3 ++ 1 :: rest]) (E := []) (k := 4) hV3 trivial
      (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
      (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  exact h1.trans (h2.trans h3)

/-- Whole copy phase: `D M P rest` with `D` empty becomes `D = 1^p`, `P` unmarked, at `XS1`. -/
theorem dcAll (p : Nat) (rest : List Nat) (hr : Sym4 rest) :
    znttLogic.Reach (hdR QNTT.DC1 [1] (List.replicate p 3 ++ 1 :: rest))
      (hd QNTT.XS1 (List.replicate p 3) (1 :: (List.replicate p 3 ++ 1 :: rest))) := by
  have h1 := dcLoop rest hr p 0 0
  have h2 := dcEnd (0 + p) (0 + p) rest hr
  simp only [Nat.zero_add, List.replicate_zero, List.nil_append] at h1 h2
  exact h1.trans h2

/-- A bit-string of `D`: cells `'0'`/`'1'`, i.e. symbols 2 and 3. -/
def BitsD (w : List Nat) : Prop := ∀ x ∈ w, x ∈ [2, 3]

theorem BitsD.sym4 {w : List Nat} (h : BitsD w) : Sym4 w := by
  intro x hx; have := h x hx; simp at this; rcases this with rfl | rfl <;> simp [ALL]

theorem BitsD.noB {w : List Nat} (h : BitsD w) : NoB w := by
  intro x hx; have := h x hx; simp at this; rcases this with rfl | rfl <;> simp [NB]

theorem BitsD.cons {a : Nat} {w : List Nat} (ha : a ∈ [2, 3]) (hw : BitsD w) : BitsD (a :: w) := by
  intro x hx; simp at hx; rcases hx with rfl | hx
  · exact ha
  · exact hw x hx

theorem BitsD.rep (k c : Nat) (hc : c ∈ [2, 3]) : BitsD (List.replicate k c) := by
  intro x hx; simp [List.mem_replicate] at hx; rw [hx.2]; exact hc

/-- `XS1` runs left across `D` to the blank. -/
theorem xs1Sweep (L R : List Nat) (hL : BitsD L) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.XS1 L R) (hdR QNTT.XS2 [] (L ++ R)) := by
  have hV : Valid [[2, 3], ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [L, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id])
    (ls' := []) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `XS5` restores the rest of `D` (cell by cell) and enters `X4` at the `M`. -/
theorem xs5Walk (A : List Nat) (Q : List Nat) (hA : Sym4 A) (hQ : Sym4 Q) :
    ∀ (D : List Nat), BitsD D →
    znttLogic.Reach (hdR QNTT.XS5 A (D ++ 1 :: Q)) (hdR QNTT.X4 (A ++ List.replicate D.length 3 ++ [1]) Q) := by
  intro D
  induction D generalizing A with
  | nil =>
    intro _
    have hV : Valid [ALL, ALL] [A, Q] := Valid.cons hA (Valid.cons hQ (Valid.nil _))
    simpa using checkFF (env := [A, Q]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id])
      (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  | cons a D ih =>
    intro hD
    have ha : a ∈ [2, 3] := hD a (by simp)
    have hD' : BitsD D := fun x hx => hD x (by simp [hx])
    have hV : Valid [ALL, ALL] [A, D ++ 1 :: Q] :=
      Valid.cons hA (Valid.cons (hD'.sym4.app (Sym4.cons (by simp [ALL]) hQ)) (Valid.nil _))
    have h1 : znttLogic.Reach (hdR QNTT.XS5 A (a :: (D ++ 1 :: Q))) (hdR QNTT.XS5 (A ++ [3]) (D ++ 1 :: Q)) := by
      simp at ha; rcases ha with rfl | rfl
      · exact checkFF (env := [A, D ++ 1 :: Q]) (E := []) (k := 4) hV trivial
          (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id])
          (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
      · exact checkFF (env := [A, D ++ 1 :: Q]) (E := []) (k := 4) hV trivial
          (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id])
          (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
    have h2 := ih (A ++ [3]) (hA.app (Sym4.cons (by simp [ALL]) Sym4.nil)) hD'
    refine h1.trans (h2.of_eq rfl ?_)
    simp [List.replicate_succ]

theorem xs2Step (a : Nat) (ha : a ∈ [2, 3]) (R : List Nat) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.XS2 [] (a :: R)) (hdR QNTT.XS3 [0] R) := by
  have hV : Valid [ALL] [R] := Valid.cons hR (Valid.nil _)
  simp at ha; rcases ha with rfl | rfl
  · exact checkFF (env := [R]) (E := []) (k := 4) hV trivial
      (ls := []) (rs := [.sym 2, .blk 0 .id]) (ls' := [.sym 0]) (rs' := [.blk 0 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [R]) (E := []) (k := 4) hV trivial
      (ls := []) (rs := [.sym 3, .blk 0 .id]) (ls' := [.sym 0]) (rs' := [.blk 0 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem xs3Step (a : Nat) (ha : a ∈ [2, 3]) (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.XS3 A (a :: R)) (hdR QNTT.XS4 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simp at ha; rcases ha with rfl | rfl
  · exact checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem xs4Step (a : Nat) (ha : a ∈ [2, 3]) (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.XS4 A (a :: R)) (hdR QNTT.XS5 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simp at ha; rcases ha with rfl | rfl
  · exact checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem xs4M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.XS4 A (1 :: R)) (hd QNTT.WX A (1 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `D` with `d + 1 ≥ 3` cells shrinks to `d` cells restored, entering the marking loop. -/
theorem xsMore (a b c : Nat) (T Q : List Nat) (ha : a ∈ [2, 3]) (hb : b ∈ [2, 3]) (hc : c ∈ [2, 3])
    (hT : BitsD T) (hQ : Sym4 Q) :
    znttLogic.Reach (hdR QNTT.XS2 [] (a :: b :: c :: (T ++ 1 :: Q)))
      (hdR QNTT.X4 (List.replicate (T.length + 2) 3 ++ [1]) Q) := by
  have s1 : Sym4 (c :: (T ++ 1 :: Q)) := Sym4.cons (by simp at hc; rcases hc with rfl | rfl <;> simp [ALL])
    (hT.sym4.app (Sym4.cons (by simp [ALL]) hQ))
  have s2 : Sym4 (T ++ 1 :: Q) := hT.sym4.app (Sym4.cons (by simp [ALL]) hQ)
  have h1 := xs2Step a ha (b :: c :: (T ++ 1 :: Q))
    (Sym4.cons (by simp at hb; rcases hb with rfl | rfl <;> simp [ALL]) s1)
  have h2 := xs3Step b hb [0] (c :: (T ++ 1 :: Q)) (Sym4.cons (by simp [ALL]) Sym4.nil) s1
  have h3 := xs4Step c hc ([0] ++ [3]) (T ++ 1 :: Q)
    ((Sym4.cons (by simp [ALL]) Sym4.nil).app (Sym4.cons (by simp [ALL]) Sym4.nil)) s2
  have h4 := xs5Walk ([0] ++ [3] ++ [3]) Q
    (((Sym4.cons (by simp [ALL]) Sym4.nil).app (Sym4.cons (by simp [ALL]) Sym4.nil)).app (Sym4.cons (by simp [ALL]) Sym4.nil))
    hQ T hT
  have h5 := h1.trans (h2.trans (h3.trans h4))
  simp only [List.cons_append, List.nil_append, List.append_assoc, hdR_z0] at h5
  simpa [List.replicate_succ, Nat.add_comm, List.append_assoc] using h5

/-- `D` with 2 cells: the divisor reaches `1`, `p` is prime. -/
theorem xsFinal (a b : Nat) (Q : List Nat) (ha : a ∈ [2, 3]) (hb : b ∈ [2, 3]) (hQ : Sym4 Q) :
    znttLogic.Reach (hdR QNTT.XS2 [] (a :: b :: 1 :: Q)) (hd QNTT.WX [0, 3] (1 :: Q)) := by
  have h1 := xs2Step a ha (b :: 1 :: Q) (Sym4.cons (by simp at hb; rcases hb with rfl | rfl <;> simp [ALL]) (Sym4.cons (by simp [ALL]) hQ))
  have h2 := xs3Step b hb [0] (1 :: Q) (Sym4.cons (by simp [ALL]) Sym4.nil) (Sym4.cons (by simp [ALL]) hQ)
  have h3 := xs4M ([0] ++ [3]) Q ((Sym4.cons (by simp [ALL]) Sym4.nil).app (Sym4.cons (by simp [ALL]) Sym4.nil)) hQ
  simpa using h1.trans (h2.trans h3)

theorem x4Mark (A : List Nat) (m : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.X4 A (List.replicate m 2 ++ 3 :: R))
      (hd QNTT.XL (A ++ List.replicate m 2) (2 :: R)) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate m 2, R] :=
    Valid.cons hA (Valid.cons (repSet m 2) (Valid.cons hR (Valid.nil _)))
  exact checkFT (env := [A, List.replicate m 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 3, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.sym 2, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem xlScan (L R : List Nat) (hL : NoB L) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.XL L R) (hdR QNTT.X1 [] (L ++ R)) := by
  have hV : Valid [NB, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [L, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id]) (ls' := []) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem x1Mark (c : Nat) (T : List Nat) (hT : Sym4 T) :
    znttLogic.Reach (hdR QNTT.X1 [] (List.replicate c 2 ++ 3 :: T))
      (hdR QNTT.X2 (List.replicate (c + 1) 2) T) := by
  have hV : Valid [[2], ALL] [List.replicate c 2, T] := Valid.cons (repSet c 2) (Valid.cons hT (Valid.nil _))
  simpa [List.replicate_succ'] using checkFF (env := [List.replicate c 2, T]) (E := []) (k := 4) hV trivial
    (ls := []) (rs := [.blk 0 .id, .sym 3, .blk 1 .id])
    (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem x2Skip (A T : List Nat) (hA : Sym4 A) (hT : Sym4 T) :
    znttLogic.Reach (hdR QNTT.X2 A (3 :: T)) (hdR QNTT.X3 (A ++ [3]) T) := by
  have hV : Valid [ALL, ALL] [A, T] := Valid.cons hA (Valid.cons hT (Valid.nil _))
  exact checkFF (env := [A, T]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem x3Walk (A : List Nat) (v : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.X3 A (List.replicate v 3 ++ 1 :: R))
      (hdR QNTT.X4 (A ++ List.replicate v 3 ++ [1]) R) := by
  have hV : Valid [ALL, [3], ALL] [A, List.replicate v 3, R] :=
    Valid.cons hA (Valid.cons (repSet v 3) (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, List.replicate v 3, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem x2Reset (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.X2 A (1 :: R)) (hd QNTT.XR A (1 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem xrSweep (d : Nat) (R : List Nat) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.XR (List.replicate d 2) R) (hdR QNTT.X3 [] (List.replicate d 3 ++ R)) := by
  have hV : Valid [[2], ALL] [List.replicate d 2, R] := Valid.cons (repSet d 2) (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [List.replicate d 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id]) (ls' := []) (rs' := [.blk 0 (.const 3), .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem s4rep (k c : Nat) (hc : c ∈ ALL) : Sym4 (List.replicate k c) := Sym4.rep k c hc

theorem noBrep (k c : Nat) (hc : c ∈ NB) : NoB (List.replicate k c) := by
  simp only [NoB_rep_iff]; exact Or.inr hc

/-- Mark one cell of `P` and one of `D` (not the last one of `D`). -/
theorem x4CycleLt (c j m : Nat) (R : List Nat) (hR : Sym4 R) :
    znttLogic.Reach
      (hdR QNTT.X4 (List.replicate c 2 ++ List.replicate (j + 2) 3 ++ [1]) (List.replicate m 2 ++ 3 :: R))
      (hdR QNTT.X4 (List.replicate (c + 1) 2 ++ List.replicate (j + 1) 3 ++ [1]) (List.replicate (m + 1) 2 ++ R)) := by
  have sD : Sym4 (List.replicate c 2 ++ List.replicate (j + 2) 3 ++ [1]) :=
    ((s4rep c 2 (by simp [ALL])).app (s4rep _ 3 (by simp [ALL]))).app (Sym4.cons (by simp [ALL]) Sym4.nil)
  have h1 := x4Mark _ m R sD hR
  have nL : NoB (List.replicate c 2 ++ List.replicate (j + 2) 3 ++ [1] ++ List.replicate m 2) := by
    simp only [NoB_app_iff, NoB_rep_iff, NoB_cons_iff, NoB_nil_iff]; simp [NB]
  have h2 := xlScan _ (2 :: R) nL (Sym4.cons (by simp [ALL]) hR)
  have e : (List.replicate c 2 ++ List.replicate (j + 2) 3 ++ [1]) ++ List.replicate m 2 ++ 2 :: R =
      List.replicate c 2 ++ 3 :: (3 :: (List.replicate j 3 ++ 1 :: (List.replicate m 2 ++ 2 :: R))) := by
    simp [List.replicate_succ, List.append_assoc]
  have sT0 : Sym4 (List.replicate j 3 ++ 1 :: (List.replicate m 2 ++ 2 :: R)) :=
    (s4rep _ 3 (by simp [ALL])).app (Sym4.cons (by simp [ALL])
      ((s4rep _ 2 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hR)))
  have sT : Sym4 (3 :: (List.replicate j 3 ++ 1 :: (List.replicate m 2 ++ 2 :: R))) :=
    Sym4.cons (by simp [ALL]) sT0
  have h3 := x1Mark c _ sT
  rw [e] at h2
  have h4 := x2Skip (List.replicate (c + 1) 2) _ (s4rep _ 2 (by simp [ALL])) sT0
  have h5 := x3Walk (List.replicate (c + 1) 2 ++ [3]) j (List.replicate m 2 ++ 2 :: R)
    ((s4rep _ 2 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) Sym4.nil))
    ((s4rep _ 2 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hR))
  have e3 : List.replicate (j + 1) 3 = 3 :: List.replicate j 3 := List.replicate_succ ..
  have e4 : List.replicate (m + 1) 2 ++ R = List.replicate m 2 ++ 2 :: R := by
    simp [List.replicate_succ']
  rw [e3, e4]
  exact (h1.trans (h2.trans (h3.trans (h4.trans h5)))).of_eq rfl (by simp)

/-- Mark the last cell of `D`: `D` is full and is reset. -/
theorem x4CycleEq (c m : Nat) (R : List Nat) (hR : Sym4 R) :
    znttLogic.Reach
      (hdR QNTT.X4 (List.replicate c 2 ++ [3] ++ [1]) (List.replicate m 2 ++ 3 :: R))
      (hdR QNTT.X4 (List.replicate (c + 1) 3 ++ [1]) (List.replicate (m + 1) 2 ++ R)) := by
  have sD : Sym4 (List.replicate c 2 ++ [3] ++ [1]) :=
    ((s4rep c 2 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) Sym4.nil)).app (Sym4.cons (by simp [ALL]) Sym4.nil)
  have h1 := x4Mark _ m R sD hR
  have nL : NoB (List.replicate c 2 ++ [3] ++ [1] ++ List.replicate m 2) := by
    simp only [NoB_app_iff, NoB_rep_iff, NoB_cons_iff, NoB_nil_iff]; simp [NB]
  have h2 := xlScan _ (2 :: R) nL (Sym4.cons (by simp [ALL]) hR)
  have sT0 : Sym4 (List.replicate m 2 ++ 2 :: R) :=
    (s4rep _ 2 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hR)
  have sT : Sym4 (1 :: (List.replicate m 2 ++ 2 :: R)) := Sym4.cons (by simp [ALL]) sT0
  have e : (List.replicate c 2 ++ [3] ++ [1]) ++ List.replicate m 2 ++ 2 :: R =
      List.replicate c 2 ++ 3 :: (1 :: (List.replicate m 2 ++ 2 :: R)) := by
    simp [List.append_assoc]
  have h3 := x1Mark c _ sT
  rw [e] at h2
  have h4 := x2Reset (List.replicate (c + 1) 2) (List.replicate m 2 ++ 2 :: R) (s4rep _ 2 (by simp [ALL]))
    sT0
  have h5 := xrSweep (c + 1) (1 :: (List.replicate m 2 ++ 2 :: R)) sT
  have h6 := x3Walk [] (c + 1) (List.replicate m 2 ++ 2 :: R) Sym4.nil sT0
  have e4 : List.replicate (m + 1) 2 ++ R = List.replicate m 2 ++ 2 :: R := by
    simp [List.replicate_succ']
  rw [e4]
  simp only [List.nil_append] at h6
  exact (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))).of_eq rfl rfl

/-- `D` with its first `c` cells marked. -/
def Dm (c d : Nat) : List Nat := List.replicate c 2 ++ List.replicate (d - c) 3

theorem x4Cycle (c d m : Nat) (R : List Nat) (hR : Sym4 R) (hc : c < d) :
    znttLogic.Reach
      (hdR QNTT.X4 (Dm c d ++ [1]) (List.replicate m 2 ++ 3 :: R))
      (hdR QNTT.X4 (Dm ((c + 1) % d) d ++ [1]) (List.replicate (m + 1) 2 ++ R)) := by
  by_cases h : c + 1 < d
  · obtain ⟨j, hj⟩ : ∃ j, d = c + j + 2 := ⟨d - c - 2, by omega⟩
    have h1 := x4CycleLt c j m R hR
    have e1 : (c + 1) % d = c + 1 := Nat.mod_eq_of_lt h
    have e2 : d - c = j + 2 := by omega
    have e3 : d - (c + 1) = j + 1 := by omega
    rw [e1]; unfold Dm; rw [e2, e3]; exact h1
  · have hd : d = c + 1 := by omega
    subst hd
    have h1 := x4CycleEq c m R hR
    have e1 : (c + 1) % (c + 1) = 0 := Nat.mod_self _
    unfold Dm; rw [e1]
    simpa using h1

theorem x4Loop (d : Nat) (rest : List Nat) (hr : Sym4 rest) :
    ∀ (k c m : Nat), c < d →
    znttLogic.Reach
      (hdR QNTT.X4 (Dm c d ++ [1]) (List.replicate m 2 ++ List.replicate k 3 ++ 1 :: rest))
      (hdR QNTT.X4 (Dm ((c + k) % d) d ++ [1]) (List.replicate (m + k) 2 ++ 1 :: rest)) := by
  intro k
  induction k with
  | zero =>
    intro c m hc
    simpa [Nat.mod_eq_of_lt hc] using LTM.Reach.refl znttLogic _
  | succ k ih =>
    intro c m hc
    have h1 := x4Cycle c d m (List.replicate k 3 ++ 1 :: rest)
      ((s4rep _ 3 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hr)) hc
    have hlt : (c + 1) % d < d := Nat.mod_lt _ (by omega)
    have h2 := ih ((c + 1) % d) (m + 1) hlt
    have e1 : List.replicate m 2 ++ List.replicate (k + 1) 3 ++ 1 :: rest =
        List.replicate m 2 ++ 3 :: (List.replicate k 3 ++ 1 :: rest) := by
      simp [List.replicate_succ]
    have e2 : ((c + 1) % d + k) % d = (c + (k + 1)) % d := by
      rw [Nat.mod_add_mod]; congr 1; omega
    have e3 : m + 1 + k = m + (k + 1) := by omega
    rw [e1]
    refine (h1.trans (h2.of_eq (by simp [List.append_assoc]) rfl)).of_eq rfl ?_
    rw [e2, e3]

/-- `P` exhausted: unmark `P`, step onto the last cell of `D`. -/
theorem x4End (c d p : Nat) (rest : List Nat) (hr : Sym4 rest) :
    znttLogic.Reach (hdR QNTT.X4 (Dm c d ++ [1]) (List.replicate p 2 ++ 1 :: rest))
      (hd QNTT.XD (Dm c d) (1 :: (List.replicate p 3 ++ 1 :: rest))) := by
  have sD : Sym4 (Dm c d ++ [1]) :=
    (((s4rep _ 2 (by simp [ALL])).app (s4rep _ 3 (by simp [ALL]))).app (Sym4.cons (by simp [ALL]) Sym4.nil))
  have sD0 : Sym4 (Dm c d) := (s4rep _ 2 (by simp [ALL])).app (s4rep _ 3 (by simp [ALL]))
  have hV : Valid [ALL, [2], ALL] [Dm c d ++ [1], List.replicate p 2, rest] :=
    Valid.cons sD (Valid.cons (repSet p 2) (Valid.cons hr (Valid.nil _)))
  have h1 : znttLogic.Reach (hdR QNTT.X4 (Dm c d ++ [1]) (List.replicate p 2 ++ 1 :: rest))
      (hd QNTT.XC (Dm c d ++ [1] ++ List.replicate p 2) (1 :: rest)) :=
    checkFT (env := [Dm c d ++ [1], List.replicate p 2, rest]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
      (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.sym 1, .blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  have hV2 : Valid [ALL, [2], ALL] [Dm c d ++ [1], List.replicate p 2, 1 :: rest] :=
    Valid.cons sD (Valid.cons (repSet p 2) (Valid.cons (Sym4.cons (by simp [ALL]) hr) (Valid.nil _)))
  have h2 : znttLogic.Reach (hd QNTT.XC (Dm c d ++ [1] ++ List.replicate p 2) (1 :: rest))
      (hd QNTT.XC (Dm c d ++ [1]) (List.replicate p 3 ++ 1 :: rest)) :=
    checkTT (env := [Dm c d ++ [1], List.replicate p 2, 1 :: rest]) (E := []) (k := 4) hV2 trivial
      (ls := [.blk 0 .id, .blk 1 .id]) (rs := [.blk 2 .id])
      (ls' := [.blk 0 .id]) (rs' := [.blk 1 (.const 3), .blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  have hV3 : Valid [ALL, ALL] [Dm c d, List.replicate p 3 ++ 1 :: rest] :=
    Valid.cons sD0 (Valid.cons ((s4rep _ 3 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hr)) (Valid.nil _))
  have h3 : znttLogic.Reach (hd QNTT.XC (Dm c d ++ [1]) (List.replicate p 3 ++ 1 :: rest))
      (hd QNTT.XD (Dm c d) (1 :: (List.replicate p 3 ++ 1 :: rest))) :=
    checkTT (env := [Dm c d, List.replicate p 3 ++ 1 :: rest]) (E := []) (k := 4) hV3 trivial
      (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
      (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  exact h1.trans (h2.trans h3)

/-- `XD`, no cell of `D` marked: `d` divides `p`; erase `D`. -/
theorem xdFull (d : Nat) (R : List Nat) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.XD (List.replicate d 3) R) (hdR QNTT.CE [] (List.replicate d 3 ++ R)) := by
  have hV : Valid [[3], ALL] [List.replicate d 3, R] := Valid.cons (repSet d 3) (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [List.replicate d 3, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id]) (ls' := []) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `XD`, some cell marked: continue with the next divisor. -/
theorem xdMarked (c v : Nat) (R : List Nat) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.XD (List.replicate c 2 ++ 2 :: List.replicate v 3) R)
      (hd QNTT.XS1 (List.replicate c 2) (2 :: (List.replicate v 3 ++ R))) := by
  have hV : Valid [[2], [3], ALL] [List.replicate c 2, List.replicate v 3, R] :=
    Valid.cons (repSet c 2) (Valid.cons (repSet v 3) (Valid.cons hR (Valid.nil _)))
  simpa using checkTT (env := [List.replicate c 2, List.replicate v 3, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 2, .blk 1 .id]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 2, .blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `CE` erases `D` and its separator, back to `PA0`. -/
theorem ceErase (d : Nat) (Q : List Nat) (hQ : Sym4 Q) :
    znttLogic.Reach (hdR QNTT.CE [] (List.replicate d 3 ++ 1 :: Q)) (hdR QNTT.PA0 [] Q) := by
  have hV : Valid [[3], ALL] [List.replicate d 3, Q] := Valid.cons (repSet d 3) (Valid.cons hQ (Valid.nil _))
  have h : znttLogic.Reach (hdR QNTT.CE [] (List.replicate d 3 ++ 1 :: Q))
      (hdR QNTT.PA0 (List.replicate d 0 ++ [0]) Q) :=
    checkFF (env := [List.replicate d 3, Q]) (E := []) (k := 4) hV trivial
      (ls := []) (rs := [.blk 0 .id, .sym 1, .blk 1 .id])
      (ls' := [.blk 0 (.const 0), .sym 0]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  rw [ZP.F.hdR_zeros _ _ _ _ (fun a ha => by
    simp [List.mem_replicate] at ha
    simp [ZP.F.B0, ha])] at h
  simp only [List.replicate_zero, List.nil_append, hdR_z0] at h
  exact h

theorem BitsD.dm (c d : Nat) (h : c ≤ d) : BitsD (Dm c d) := by
  intro x hx
  simp only [Dm, List.mem_append, List.mem_replicate] at hx
  rcases hx with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp

theorem Dm_length (c d : Nat) (h : c ≤ d) : (Dm c d).length = d := by
  simp [Dm]; omega

/-- The trial-division loop.  `D` is a bit-string of length `e` (just left of its separator). -/
theorem testRun (p : Nat) (rest : List Nat) (hr : Sym4 rest) (hp : 2 ≤ p) :
    ∀ (e : Nat), 2 ≤ e → ∀ D : List Nat, BitsD D → D.length = e →
    ((∀ d, 2 ≤ d → d < e → ¬ d ∣ p) →
      znttLogic.Reach (hdR QNTT.XS2 [] (D ++ 1 :: (List.replicate p 3 ++ 1 :: rest)))
        (hd QNTT.WX [0, 3] (1 :: (List.replicate p 3 ++ 1 :: rest)))) ∧
    ((∃ d, 2 ≤ d ∧ d < e ∧ d ∣ p) →
      znttLogic.Reach (hdR QNTT.XS2 [] (D ++ 1 :: (List.replicate p 3 ++ 1 :: rest)))
        (hdR QNTT.PA0 [] (List.replicate p 3 ++ 1 :: rest))) := by
  intro e he
  obtain ⟨n, rfl⟩ : ∃ n, e = n + 2 := ⟨e - 2, by omega⟩
  induction n with
  | zero =>
    intro D hD hl
    rcases D with _ | ⟨a, _ | ⟨b, _ | ⟨x, D⟩⟩⟩
    · simp at hl
    · simp at hl
    · refine ⟨fun _ => ?_, fun ⟨d, h1, h2, _⟩ => by omega⟩
      exact xsFinal a b (List.replicate p 3 ++ 1 :: rest) (hD a (by simp)) (hD b (by simp))
        ((s4rep _ 3 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hr))
    · simp at hl
  | succ n ih =>
    intro D hD hl
    obtain ⟨e, he⟩ : ∃ e, e = n + 2 := ⟨_, rfl⟩
    have he1 : n + 1 + 2 = e + 1 := by omega
    rw [he1] at hl ⊢
    rw [← he] at ih
    have ih := ih (by omega)
    have he2 : 2 ≤ e := by omega
    rcases D with _ | ⟨a, _ | ⟨b, _ | ⟨c, T⟩⟩⟩
    · exact absurd hl (by simp)
    · exact absurd hl (by simp <;> omega)
    · exact absurd hl (by simp <;> omega)
    · have hTl : T.length = e - 2 := by simp at hl; omega
      have hT : BitsD T := fun x hx => hD x (by simp [hx])
      have ha := hD a (by simp)
      have hb := hD b (by simp)
      have hc := hD c (by simp)
      have sQ : Sym4 (List.replicate p 3 ++ 1 :: rest) :=
        (s4rep _ 3 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hr)
      have h1 := xsMore a b c T _ ha hb hc hT sQ
      have hlen : T.length + 2 = e := by omega
      rw [hlen] at h1
      have hDm0 : List.replicate e 3 = Dm 0 e := by simp [Dm]
      have h2 := x4Loop e rest hr p 0 0 (by omega)
      have hcl : (0 + p) % e < e := Nat.mod_lt _ (by omega)
      simp only [List.replicate_zero, List.nil_append, Nat.zero_add, ← hDm0] at h2
      rw [hDm0] at h1
      have h3 := x4End (p % e) e p rest hr
      have h123 := h1.trans (h2.trans h3)
      by_cases hdiv : p % e = 0
      · -- e divides p
        have hed : e ∣ p := Nat.dvd_of_mod_eq_zero hdiv
        rw [hdiv] at h123
        have h4 := xdFull e (1 :: (List.replicate p 3 ++ 1 :: rest))
          (Sym4.cons (by simp [ALL]) sQ)
        have h5 := ceErase e _ sQ
        have hDe : Dm 0 e = List.replicate e 3 := by simp [Dm]
        rw [hDe] at h123
        have hfin := h123.trans (h4.trans h5)
        refine ⟨fun hn => ?_, fun _ => hfin⟩
        exact absurd hed (hn e (by omega) (by omega))
      · obtain ⟨c', hc'⟩ : ∃ c', p % e = c' + 1 := ⟨p % e - 1, by omega⟩
        have hlt : p % e < e := Nat.mod_lt _ (by omega)
        rw [hc'] at h123
        have hDm : Dm (c' + 1) e = List.replicate c' 2 ++ 2 :: List.replicate (e - (c' + 1)) 3 := by
          simp [Dm, List.replicate_succ']
        rw [hDm] at h123
        have h4 := xdMarked c' (e - (c' + 1)) (1 :: (List.replicate p 3 ++ 1 :: rest))
          (Sym4.cons (by simp [ALL]) sQ)
        have h5 := xs1Sweep (List.replicate c' 2) (2 :: (List.replicate (e - (c' + 1)) 3 ++ 1 :: (List.replicate p 3 ++ 1 :: rest)))
          (BitsD.rep _ _ (by simp)) (by
            exact Sym4.cons (by simp [ALL]) ((s4rep _ 3 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) sQ)))
        have hDm' : BitsD (Dm (c' + 1) e) := BitsD.dm _ _ (by omega)
        have hlen' : (Dm (c' + 1) e).length = e := Dm_length _ _ (by omega)
        obtain ⟨ihA, ihB⟩ := ih (Dm (c' + 1) e) hDm' hlen'
        have hmid := h123.trans (h4.trans h5)
        have e5 : Dm (c' + 1) e ++ 1 :: (List.replicate p 3 ++ 1 :: rest) =
            List.replicate c' 2 ++ 2 :: (List.replicate (e - (c' + 1)) 3 ++ 1 :: (List.replicate p 3 ++ 1 :: rest)) := by
          rw [hDm]; simp
        have hmid' : znttLogic.Reach (hdR QNTT.XS2 [] (a :: b :: c :: (T ++ 1 :: (List.replicate p 3 ++ 1 :: rest))))
            (hdR QNTT.XS2 [] (Dm (c' + 1) e ++ 1 :: (List.replicate p 3 ++ 1 :: rest))) :=
          hmid.of_eq rfl (by rw [e5])
        refine ⟨fun hn => ?_, fun ⟨d, hd2, hd3, hdd⟩ => ?_⟩
        · exact hmid'.trans (ihA (fun d h2 h3 => hn d h2 (by omega)))
        · have hne : d ≠ e := by
            rintro rfl
            exact absurd (Nat.mod_eq_zero_of_dvd hdd) hdiv
          exact hmid'.trans (ihB ⟨d, hd2, by omega, hdd⟩)

theorem isPrimeN_iff (p : Nat) :
    isPrimeN p = true ↔ 2 ≤ p ∧ ∀ d, 2 ≤ d → d < p → ¬ d ∣ p := by
  simp only [isPrimeN, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true]
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun d hd hdp hdv => ?_⟩
    rcases h d hdp with h | h
    · omega
    · simp at h; exact h (Nat.mod_eq_zero_of_dvd hdv)
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun d hd => ?_⟩
    by_cases h3 : d < 2
    · exact Or.inl (by omega)
    · refine Or.inr ?_
      have := h d (by omega) hd
      simp
      intro h0; exact this (Nat.dvd_of_mod_eq_zero h0)

/-- The primality ruler: `P` runs over `1 + n i` until it is prime. -/
theorem primeRuler (n : Nat) (hn : 1 ≤ n) (Mid Z : List Nat) (hM : NoB Mid) (hZ : Sym4 Z) :
    ∀ (t i0 j p0 : Nat), j + p0 = 1 + n * i0 →
    (∃ i, i0 < i ∧ i ≤ i0 + t ∧ isPrimeN (1 + n * i) = true) →
    ∃ i, i0 < i ∧ isPrimeN (1 + n * i) = true ∧
      (∀ i', i0 < i' → i' < i → isPrimeN (1 + n * i') = false) ∧
      znttLogic.Reach
        (hdR QNTT.PA0 (List.replicate j 3)
          (List.replicate p0 3 ++ 1 :: (Mid ++ 1 :: List.replicate n 3) ++ 0 :: Z))
        (hd QNTT.WX [0, 3] (1 :: (List.replicate (1 + n * i) 3 ++ 1 :: ((Mid ++ 1 :: List.replicate n 3) ++ 0 :: Z)))) := by
  intro t
  induction t with
  | zero => intro i0 j p0 _ ⟨i, h1, h2, _⟩; omega
  | succ t ih =>
    intro i0 j p0 hj hex
    have hpad := padd Mid Z hM hZ j p0 n
    have hp : j + p0 + n = 1 + n * (i0 + 1) := by rw [hj, Nat.mul_add]; omega
    have hp2 : 2 ≤ j + p0 + n := by omega
    have hrest : Sym4 ((Mid ++ 1 :: List.replicate n 3) ++ 0 :: Z) :=
      (hM.sym4.app (Sym4.cons (by simp [ALL]) (s4rep _ 3 (by simp [ALL])))).app (Sym4.cons (by simp [ALL]) hZ)
    have hdc := dcAll (j + p0 + n) _ hrest
    have hxs := xs1Sweep (List.replicate (j + p0 + n) 3) (1 :: (List.replicate (j + p0 + n) 3 ++ 1 :: ((Mid ++ 1 :: List.replicate n 3) ++ 0 :: Z)))
      (BitsD.rep _ _ (by simp)) (Sym4.cons (by simp [ALL]) ((s4rep _ 3 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hrest)))
    have hrun := testRun (j + p0 + n) _ hrest hp2 (j + p0 + n) hp2 (List.replicate (j + p0 + n) 3)
      (BitsD.rep _ _ (by simp)) (by simp)
    simp only [List.append_assoc, List.cons_append] at hpad hdc hxs hrun ⊢
    have hstart := hpad.trans (hdc.trans hxs)
    by_cases hpr : isPrimeN (1 + n * (i0 + 1)) = true
    · refine ⟨i0 + 1, by omega, hpr, fun i' h1 h2 => by omega, ?_⟩
      rw [← hp] at hpr
      have hno := ((isPrimeN_iff _).1 hpr).2
      have := hstart.trans (hrun.1 (fun d h2 h3 => hno d h2 h3))
      rw [hp] at this
      exact this
    · have hcomp : ∃ d, 2 ≤ d ∧ d < j + p0 + n ∧ d ∣ j + p0 + n := by
        by_cases h : ∃ d, 2 ≤ d ∧ d < j + p0 + n ∧ d ∣ j + p0 + n
        · exact h
        · exfalso
          apply hpr
          rw [← hp, isPrimeN_iff]
          refine ⟨hp2, fun d h2 h3 hd => h ⟨d, h2, h3, hd⟩⟩
      have hnext := hstart.trans (hrun.2 hcomp)
      obtain ⟨i, hi0, hi1, hi2⟩ := hex
      have hi : i0 + 1 < i := by
        rcases Nat.lt_or_ge (i0 + 1) i with h | h
        · exact h
        · exfalso; have : i = i0 + 1 := by omega
          subst this; exact hpr hi2
      obtain ⟨i', h1, h2, h3, h4⟩ := ih (i0 + 1) 0 (j + p0 + n) (by simpa using hp) ⟨i, hi, by omega, hi2⟩
      refine ⟨i', by omega, h2, fun x hx1 hx2 => ?_, ?_⟩
      · rcases Nat.lt_or_ge (i0 + 1) x with h | h
        · exact h3 x h hx2
        · have : x = i0 + 1 := by omega
          subst this; simpa using hpr
      · rw [hp] at hnext h4
        simp only [List.append_assoc, List.cons_append, List.replicate_zero] at hnext h4 ⊢
        exact hnext.trans h4

/-- Under `PrimeEx`, from `P = 1` the ruler ends with `P = primeN n` at `WX`. -/
theorem primeRuler_primeN (hex : PrimeEx) (n : Nat) (hn : 1 ≤ n) (Mid Z : List Nat)
    (hM : NoB Mid) (hZ : Sym4 Z) :
    znttLogic.Reach
      (hdR QNTT.PA0 (List.replicate 1 3)
        (List.replicate 0 3 ++ 1 :: (Mid ++ 1 :: List.replicate n 3) ++ 0 :: Z))
      (hd QNTT.WX [0, 3] (1 :: (List.replicate (primeN n) 3 ++ 1 :: ((Mid ++ 1 :: List.replicate n 3) ++ 0 :: Z)))) := by
  obtain ⟨i, hi1, hi2⟩ := hex n hn
  obtain ⟨i1, hi1', hp1, hpn, hmin⟩ := primeN_spec n ⟨i, hi1, hi2⟩
  obtain ⟨i', h0, hpr, hbef, hrun⟩ :=
    primeRuler n hn Mid Z hM hZ i 0 1 0 (by simp) ⟨i, by omega, by omega, hi2⟩
  have hle : i1 ≤ i' := hmin i' (by omega) hpr
  have hle2 : i' ≤ i1 := by
    rcases Nat.lt_or_ge i1 i' with h | h
    · have := hbef i1 (by omega) h
      rw [hp1] at this; cases this
    · exact h
  have : i' = i1 := by omega
  subst this
  rw [hpn]
  exact hrun

end ZP.NTT
