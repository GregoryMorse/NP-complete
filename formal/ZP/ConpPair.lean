module

public import ZP.ConpGad
public import ZP.ConpSearch
public import ZP.DefsConp

@[expose] public section

/-!
# Z_coNP: the outer machine for `zconpLogic`

Fuel builds, run setup (with `core`), the search over the choice string `D`, the two phases and one pair.
-/

namespace ZP.Conp

open ZP

theorem Bits.rev {u : List Nat} (h : Bits u) : Bits u.reverse := fun a ha => h a (List.mem_reverse.mp ha)

theorem o13_noB {T : List Nat} (h : ∀ a ∈ T, a ∈ O13) : NoB T := fun a ha => by
  have := h a ha
  simp [O13] at this
  simp [NB]
  omega

theorem t3_noB {T : List Nat} (h : ∀ a ∈ T, a ∈ T3) : NoB T := fun a ha => by
  have := h a ha
  simp [T3] at this
  simp [NB]
  omega

theorem z2_noB {T : List Nat} (h : ∀ a ∈ T, a ∈ Z2) : NoB T := fun a ha => by
  have := h a ha
  simp [Z2] at this
  simp [NB]
  omega

theorem rep_t3 (k : Nat) : ∀ a ∈ List.replicate k 3, a ∈ T3 := fun a ha => by
  rw [List.eq_of_mem_replicate ha]; simp [T3]

theorem rep_z2 (k : Nat) : ∀ a ∈ List.replicate k 2, a ∈ Z2 := fun a ha => by
  rw [List.eq_of_mem_replicate ha]; simp [Z2]

theorem one_nb : (1 : Nat) ∈ NB := by simp [NB]

theorem rep_snoc_eq (n a : Nat) : List.replicate n a ++ [a] = a :: List.replicate n a := by
  have := rep_cons_comm a [] n
  simpa using this

theorem bitsOf_nil : bitsOf [] = [] := rfl

theorem bitsOf_reverse (l : List Bool) : bitsOf l.reverse = (bitsOf l).reverse := by
  simp [bitsOf]

theorem bitsOf_len (l : List Bool) : (bitsOf l).length = l.length := by
  simp [bitsOf]

theorem blkW_full (n : Nat) : blkW n (n + 1) = 1 :: List.replicate (n + 1) 3 := by
  simp [blkW]

theorem FWr_full_o13 (n : Nat) : ∀ i, ∀ a ∈ FWr n (List.replicate i (n + 1)), a ∈ O13
  | 0 => fun _ h => by cases h
  | i + 1 => by
    intro a ha
    have e : FWr n (List.replicate (i + 1) (n + 1)) = FWr n (List.replicate i (n + 1)) ++ blkW n (n + 1) := rfl
    rw [e] at ha
    rcases List.mem_append.mp ha with h | h
    · exact FWr_full_o13 n i a h
    · rw [blkW_full] at h
      rcases List.mem_cons.mp h with rfl | h
      · simp [O13]
      · rw [List.eq_of_mem_replicate h]; simp [O13]

/-! ## Loops of the outer machine -/
theorem wbBody (Jl : List Nat) (Y : List Nat) (b : Nat) (hJl : Bits Jl) (hY : Sym4 Y) (hb : b ∈ bits) :
    zconpLogic.Reach (hd Q.WB1 (Jl ++ (b :: [1])) Y)
      (hd Q.WB1 (Jl ++ [1]) (b :: Y)) := by
  have hV : Valid [bits, ALL] [Jl, Y] := Valid.cons hJl (Valid.cons hY (Valid.nil _))
  rcases mem_bits hb with rfl | rfl
  · exact checkTT (env := [Jl, Y]) (E := []) (k := 3) hV trivial
      (ls := [.blk 0 .id, .sym 2, .sym 1]) (rs := [.blk 1 .id])
      (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 2, .blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkTT (env := [Jl, Y]) (E := []) (k := 3) hV trivial
      (ls := [.blk 0 .id, .sym 3, .sym 1]) (rs := [.blk 1 .id])
      (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 3, .blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem wbEnd (j : List Nat) (Y : List Nat) (hj : Bits j) (hY : Sym4 Y) :
    zconpLogic.Reach (hd Q.WB1 [1] (j ++ (1 :: Y)))
      (hdR Q.GC (1 :: (1 :: (j ++ [1]))) Y) := by
  have hV : Valid [bits, ALL] [j, Y] := Valid.cons hj (Valid.cons hY (Valid.nil _))
  exact checkTF (env := [j, Y]) (E := []) (k := 5) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id])
    (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gcBody (Ur : List Nat) (V : List Nat) (P : List Nat) (u : List Nat) (v : List Nat) (Rest : List Nat) (b : Nat) (hUr : Bits Ur) (hV : NoB V) (hP : Bits P) (hu : Bits u) (hv : Bits v) (hRest : Sym4 Rest) (hb : b ∈ bits) :
    zconpLogic.Reach (hdR Q.GC (Ur ++ (1 :: (V ++ (P ++ (1 :: u))))) (b :: (v ++ (1 :: Rest))))
      (hdR Q.GC (b :: (Ur ++ (1 :: (V ++ (P ++ (1 :: (u ++ [b]))))))) (v ++ (1 :: Rest))) := by
  have hV : Valid [bits, NB, bits, bits, bits, ALL] [Ur, V, P, u, v, Rest] := Valid.cons hUr (Valid.cons hV (Valid.cons hP (Valid.cons hu (Valid.cons hv (Valid.cons hRest (Valid.nil _))))))
  rcases mem_bits hb with rfl | rfl
  · exact checkFF (env := [Ur, V, P, u, v, Rest]) (E := []) (k := 15) hV trivial
      (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [.sym 2, .blk 4 .id, .sym 1, .blk 5 .id])
      (ls' := [.sym 2, .blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id, .sym 1, .blk 3 .id, .sym 2]) (rs' := [.blk 4 .id, .sym 1, .blk 5 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Ur, V, P, u, v, Rest]) (E := []) (k := 15) hV trivial
      (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [.sym 3, .blk 4 .id, .sym 1, .blk 5 .id])
      (ls' := [.sym 3, .blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id, .sym 1, .blk 3 .id, .sym 3]) (rs' := [.blk 4 .id, .sym 1, .blk 5 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
theorem gcLoop (V P Rest : List Nat) (hV : NoB V) (hP : Bits P) (hR : Sym4 Rest) :
    ∀ v u, Bits u → Bits v →
      zconpLogic.Reach (hdR Q.GC (u.reverse ++ 1 :: (V ++ (P ++ 1 :: u))) (v ++ 1 :: Rest))
        (hdR Q.GC ((u ++ v).reverse ++ 1 :: (V ++ (P ++ 1 :: (u ++ v)))) (1 :: Rest))
  | [], u, _, _ => by
    rw [List.append_nil, List.nil_append]
    exact LTM.Reach.refl _ _
  | b :: v, u, hu, hv => by
    have h1 := gcBody u.reverse V P u v Rest b hu.rev hV hP hu hv.tail hR hv.head
    have h2 := gcLoop V P Rest hV hP hR v (u ++ [b]) (hu.snoc hv.head) hv.tail
    exact h1.trans (h2.ofEq (by simp) (by simp only [List.append_assoc, List.singleton_append]))

theorem wbLoop : ∀ (jr Y : List Nat), Bits jr → Sym4 Y →
    zconpLogic.Reach (hd Q.WB1 (jr.reverse ++ [1]) Y) (hd Q.WB1 [1] (jr.reverse ++ Y))
  | [], Y, _, _ => LTM.Reach.refl _ _
  | b :: jr, Y, hj, hY => by
    have h1 := wbBody jr.reverse Y b hj.tail.rev hY hj.head
    have h2 := wbLoop jr (b :: Y) hj.tail (Sym4.cons (bits_all hj.head) hY)
    exact (h1.ofEq (by simp) rfl).trans (h2.ofEq rfl (by simp))

/-! ## Binary counters (least significant bit first) -/

def bitN : Bool → Nat
  | true => 1
  | false => 0

theorem bitN_le (b : Bool) : bitN b ≤ 1 := by cases b <;> decide

/-! ## Shortlex successor -/

/-- Successor of a bit string given least significant bit first. -/
def incR : List Bool → List Bool
  | [] => [false]
  | false :: r => true :: r
  | true :: r => false :: incR r

/-- `1 r.reverse` read in binary. -/
def numR : List Bool → Nat
  | [] => 1
  | b :: r => bitN b + 2 * numR r

theorem numR_inc : ∀ r, numR (incR r) = numR r + 1
  | [] => rfl
  | false :: r => by
    show 1 + 2 * numR r = 0 + 2 * numR r + 1
    omega
  | true :: r => by
    have := numR_inc r
    show 0 + 2 * numR (incR r) = 1 + 2 * numR r + 1
    omega

theorem numR_gt : ∀ r, r.length < numR r
  | [] => by decide
  | b :: r => by
    have := numR_gt r
    show r.length + 1 < bitN b + 2 * numR r
    omega

theorem strAux_numR : ∀ (r : List Bool) (f : Nat) (acc : List Bool), r.length ≤ f →
    strAux f (numR r) acc = r.reverse ++ acc
  | [], 0, _, _ => rfl
  | [], f + 1, acc, _ => by simp [strAux, numR]
  | b :: r, 0, _, h => absurd h (by simp)
  | b :: r, f + 1, acc, h => by
    have hg := numR_gt r
    have hb := bitN_le b
    have hN : ¬ numR (b :: r) ≤ 1 := by
      show ¬ (bitN b + 2 * numR r ≤ 1)
      omega
    have h2 : numR (b :: r) / 2 = numR r := by
      show (bitN b + 2 * numR r) / 2 = numR r
      omega
    have h3 : (numR (b :: r) % 2 == 1) = b := by
      cases b
      · have e : (bitN false + 2 * numR r) % 2 = 0 := by
          show (0 + 2 * numR r) % 2 = 0
          omega
        show ((bitN false + 2 * numR r) % 2 == 1) = false
        rw [e]
        rfl
      · have e : (bitN true + 2 * numR r) % 2 = 1 := by
          show (1 + 2 * numR r) % 2 = 1
          omega
        show ((bitN true + 2 * numR r) % 2 == 1) = true
        rw [e]
        rfl
    show (if numR (b :: r) ≤ 1 then acc
      else strAux f (numR (b :: r) / 2) ((numR (b :: r) % 2 == 1) :: acc)) = _
    rw [ite_eq_right hN, h2, h3, strAux_numR r f (b :: acc) (by simp at h; omega)]
    simp

theorem str_numR (r : List Bool) : str (numR r) = r.reverse := by
  have := numR_gt r
  show strAux (numR r) (numR r) [] = _
  rw [strAux_numR r _ [] (by omega), List.append_nil]

theorem numR_surj_aux : ∀ f N, 1 ≤ N → N ≤ f → ∃ r, numR r = N
  | 0, N, h, hf => absurd hf (by omega)
  | f + 1, N, h, hf => by
    by_cases h1 : N = 1
    · exact ⟨[], by rw [h1]; rfl⟩
    · obtain ⟨r, hr⟩ := numR_surj_aux f (N / 2) (by omega) (by omega)
      refine ⟨(N % 2 == 1) :: r, ?_⟩
      show bitN (N % 2 == 1) + 2 * numR r = N
      rw [hr]
      rcases Nat.mod_two_eq_zero_or_one N with h2 | h2
      · rw [h2]
        show 0 + 2 * (N / 2) = N
        omega
      · rw [h2]
        show 1 + 2 * (N / 2) = N
        omega

theorem numR_surj (N : Nat) (h : 1 ≤ N) : ∃ r, numR r = N := numR_surj_aux N N h (Nat.le_refl _)

theorem str_one : str 1 = [] := rfl

/-! ## Bit strings -/

theorem bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  revert h
  cases a <;> cases b <;> decide


/-! ## Fuel builds -/

theorem copyLoopY (P T Y : List Nat) (hP : NoB P) (hT : NoB T) (hY : Sym4 Y) :
    ∀ v u, Bits u → Bits v →
      zconpLogic.Reach
        (hdR Q.COPY (P ++ u) (v ++ 1 :: (T ++ 1 :: (List.replicate u.length 3 ++ (List.replicate (v.length + 1) 0 ++ Y)))))
        (hdR Q.COPY (P ++ (u ++ v)) (1 :: (T ++ 1 :: (List.replicate (u ++ v).length 3 ++ 0 :: Y))))
  | [], u, _, _ => by
    simp only [List.append_nil, List.length_nil, Nat.zero_add, List.replicate_one, List.singleton_append]
    exact LTM.Reach.refl _ _
  | b :: v, u, hu, hv => by
    have h1 := copyBodyY P u v T Y b hP hu hv.tail hT hY hv.head
    have h2 := copyLoopY P T Y hP hT hY v (u ++ [b]) (hu.snoc hv.head) hv.tail
    refine (h1.ofEq (by simp [List.replicate_succ]) rfl).trans (h2.ofEq ?_ (by simp))
    have e3 : List.replicate (u ++ [b]).length 3 = List.replicate u.length 3 ++ [3] := by
      simp [List.replicate_succ']
    have e0 : List.replicate (v.length + 1) 0 = 0 :: List.replicate v.length 0 := rfl
    rw [e3, e0]
    simp

theorem blkCopyY (Jl Jr s T Y : List Nat) (hJl : Bits Jl) (hJr : Bits Jr) (hs : Bits s) (hT : NoB T)
    (hY : Sym4 Y) :
    zconpLogic.Reach (hdR Q.GRB (Jl ++ 1 :: (Jr ++ 1 :: (s ++ 1 :: T))) (0 :: (0 :: (List.replicate s.length 0 ++ Y))))
      (hdR Q.COPY (Jl ++ 1 :: (Jr ++ 1 :: s)) (1 :: (T ++ 1 :: (List.replicate s.length 3 ++ 0 :: Y)))) := by
  have hP : NoB (Jl ++ 1 :: (Jr ++ [1])) :=
    hJl.noB.app (NoB.cons one_nb (hJr.noB.app (NoB.cons one_nb NoB.nil)))
  have h1 := blkStartY Jl Jr s T Y hJl hJr hs hT hY
  have h2 := copyLoopY (Jl ++ 1 :: (Jr ++ [1])) T Y hP hT hY s [] Bits.nil hs
  refine h1.trans (h2.ofEq (by simp [List.replicate_succ]) ?_)
  simp

/-- The verifier's fuel: one block. -/
theorem vBuild (j s Dw : List Nat) (hj : Bits j) (hs : Bits s) (hD : NoB Dw) :
    zconpLogic.Reach
      (hdR Q.GRB (1 :: (j ++ 1 :: (s ++ [1, 1]))) (List.replicate (s.length + 2) 0 ++ 0 :: Dw))
      (hdR Q.GC (1 :: 1 :: (j ++ 1 :: (s ++ [1]))) (1 :: (FWr s.length [s.length + 1] ++ 0 :: Dw))) := by
  have hY : Sym4 (0 :: Dw) := Sym4.cons (by simp [ALL]) hD.sym4
  have h1 := blkCopyY [] j s [1] (0 :: Dw) Bits.nil hj hs (NoB.cons one_nb NoB.nil) hY
  have h2 := blkVerY j s (0 :: Dw) hj hs hY
  have h1' : zconpLogic.Reach
      (hdR Q.GRB (1 :: (j ++ 1 :: (s ++ [1, 1]))) (List.replicate (s.length + 2) 0 ++ 0 :: Dw))
      (hdR Q.COPY (1 :: (j ++ 1 :: s)) (1 :: 1 :: 1 :: (List.replicate s.length 3 ++ 0 :: 0 :: Dw))) :=
    h1.ofEq (by simp [List.replicate_succ]) (by simp)
  have e : (1 :: 1 :: (List.replicate s.length 3 ++ 3 :: 0 :: Dw) : List Nat) =
      1 :: (FWr s.length [s.length + 1] ++ 0 :: Dw) := by
    simp [FWr, blkW, List.replicate_succ']
  exact h1'.trans (h2.ofEq rfl (by rw [e]))

end ZP.Conp
