module

public import ZP.MHDec

@[expose] public section

/-!
# The far-right erase loops (shared by `Z_LP` and `Z_LNL`)

At the far right the storage (and the fuel) is erased by a two-state loop (`EAs`/`EX`, `VA3`/`EY`): a
non-blank cell is blanked, a blank is passed, and two consecutive blanks end the loop. The loop works on every
list in which no two consecutive cells are blank (`Eras`). The statements are generic in the machine and the
states; the single steps come from the generated segments of the machine.
-/

namespace ZP.MH

open ZP

theorem hd_trail0 (q : Nat) (A R : List Nat) : hd q A (R ++ [0]) = hd q A R := by
  rw [hd_eq', hd_eq', sapp_lead0]

theorem hdR_zeros (q : Nat) (A : List Nat) : ∀ m : Nat, hdR q A (List.replicate m 0) = hdR q A []
  | 0 => rfl
  | m + 1 => by
    rw [List.replicate_succ', hdR_trail0, hdR_zeros q A m]

theorem hd_zeros (q : Nat) (A : List Nat) : ∀ m : Nat, hd q A (List.replicate m 0) = hd q A []
  | 0 => rfl
  | m + 1 => by
    rw [List.replicate_succ', hd_trail0, hd_zeros q A m]

theorem hd_snoc (q : Nat) (A : List Nat) (a : Nat) (R : List Nat) : hd q (A ++ [a]) R = hdR q A (a :: R) := by
  rw [hd_eq', hdR_eq']
  simp [List.reverse_append, sapp, scons]
  rfl

/-- Lists without two consecutive blanks (a blank is followed by a non-blank cell or the end). -/
inductive Eras : List Nat → Prop
  | nil : Eras []
  | nb {c : Nat} {S : List Nat} : c ∈ NB → Eras S → Eras (c :: S)
  | bl {S : List Nat} : Eras S → (S = [] ∨ ∃ c S', S = c :: S' ∧ c ∈ NB) → Eras (0 :: S)

theorem Eras.sym4 : ∀ {S : List Nat}, Eras S → Sym4 S
  | _, .nil => Sym4.nil
  | _, .nb hc h => Sym4.cons (by simp [NB] at hc; simp [ALL]; omega) h.sym4
  | _, .bl h _ => Sym4.cons (by simp [ALL]) h.sym4

theorem Eras.of_noB : ∀ {W : List Nat}, NoB W → Eras W
  | [], _ => .nil
  | c :: W, h => .nb (h c (List.mem_cons_self ..)) (Eras.of_noB (fun a ha => h a (List.mem_cons_of_mem _ ha)))

theorem Eras.app_nb : ∀ {W S : List Nat}, NoB W → Eras S → Eras (W ++ S)
  | [], S, _, hS => hS
  | c :: W, S, h, hS =>
    .nb (h c (List.mem_cons_self ..)) (Eras.app_nb (fun a ha => h a (List.mem_cons_of_mem _ ha)) hS)

theorem Eras.gap {S : List Nat} (h : Eras S) (hh : S = [] ∨ ∃ c S', S = c :: S' ∧ c ∈ NB) : Eras (0 :: S) :=
  .bl h hh

theorem Eras.tail_nb {c : Nat} {S : List Nat} (hc : c ∈ NB) (h : Eras (c :: S)) : Eras S := by
  cases h with
  | nb _ h' => exact h'
  | bl _ _ => simp [NB] at hc

/-- The loop: `qa` after a non-blank cell, `qx` after a blank, ended in `qn`. -/
theorem eraseLoop (L : LTM) (qa qx qn : Nat)
    (hN : ∀ c, c ∈ NB → ∀ A R, Sym4 A → Sym4 R → L.Reach (hdR qa A (c :: R)) (hdR qa (A ++ [0]) R))
    (hB : ∀ A R, Sym4 A → Sym4 R → L.Reach (hdR qa A (0 :: R)) (hdR qx (A ++ [0]) R))
    (hX : ∀ c, c ∈ NB → ∀ A R, Sym4 A → Sym4 R → L.Reach (hdR qx A (c :: R)) (hdR qa (A ++ [0]) R))
    (hXE : ∀ A, Sym4 A → L.Reach (hdR qx A []) (hd qn A [0]))
    (hAE : ∀ A, Sym4 A → L.Reach (hdR qa A []) (hd qn (A ++ [0]) [0])) :
    ∀ n S, S.length = n → Eras S → ∀ A, Sym4 A →
      ∃ m, L.Reach (hdR qa A S) (hd qn (A ++ List.replicate m 0) [0]) := by
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro S hn hS A hA
    cases hS with
    | nil => exact ⟨1, (hAE A hA).ofEq rfl (by simp)⟩
    | nb hc hS' =>
      have hA' : Sym4 (A ++ [0]) := hA.app (Sym4.cons h0 Sym4.nil)
      obtain ⟨m, h⟩ := ih _ (by simp at hn; omega) _ rfl hS' (A ++ [0]) hA'
      exact ⟨m + 1, (hN _ hc A _ hA hS'.sym4).trans (h.ofEq rfl (by simp [List.replicate_succ]))⟩
    | bl hX' hh =>
      have hA' : Sym4 (A ++ [0]) := hA.app (Sym4.cons h0 Sym4.nil)
      rcases hh with rfl | ⟨c, S'', rfl, hc⟩
      · exact ⟨1, ((hB A [] hA Sym4.nil).trans (hXE (A ++ [0]) hA')).ofEq rfl (by simp)⟩
      · have hS'' : Eras S'' := Eras.tail_nb hc hX'
        have hA'' : Sym4 (A ++ [0] ++ [0]) := hA'.app (Sym4.cons h0 Sym4.nil)
        obtain ⟨m, h⟩ := ih S''.length (by simp at hn; omega) S'' rfl hS'' (A ++ [0] ++ [0]) hA''
        have h1 := (hB A (c :: S'') hA hX'.sym4).trans (hX c hc (A ++ [0]) S'' hA' hS''.sym4)
        exact ⟨m + 2, h1.trans (h.ofEq rfl (by simp [List.replicate_succ]))⟩

/-- Going back over `m` erased cells. -/
theorem skipBack (L : LTM) (qn : Nat)
    (hS : ∀ A R, Sym4 A → Sym4 R → L.Reach (hd qn (A ++ [0]) R) (hd qn A ([0] ++ R))) :
    ∀ m A R, Sym4 A → Sym4 R →
      L.Reach (hd qn (A ++ List.replicate m 0) R) (hd qn A (List.replicate m 0 ++ R))
  | 0, A, R, _, _ => by simpa using LTM.Reach.refl L _
  | m + 1, A, R, hA, hR => by
    have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
    have hz : Sym4 (List.replicate m 0) := Sym4.rep m 0 h0
    have h1 := hS (A ++ List.replicate m 0) R (hA.app hz) hR
    have h2 := skipBack L qn hS m A ([0] ++ R) hA (Sym4.cons h0 hR)
    exact (h1.ofEq (by simp [List.replicate_succ']) rfl).trans
      (h2.ofEq rfl (by simp [List.replicate_succ, rep_cons_comm]))

/-! ## The storage is erasable -/

theorem Eras_uc0 {u : List Nat} (hu : Bits u) (p : Nat) {S : List Nat} (hS : Eras S)
    (hSh : S = [] ∨ ∃ S', S = 1 :: S') : Eras (uc u p 0 ++ S) := by
  have hT : NoB (u.take p) := (Bits.noB (fun a ha => hu a (List.mem_of_mem_take ha)))
  have hD : NoB (u.drop p) := (Bits.noB (fun a ha => hu a (List.mem_of_mem_drop ha)))
  have e : uc u p 0 ++ S = 1 :: (u.take p ++ 0 :: (u.drop p ++ S)) := by simp [uc]
  rw [e]
  refine .nb one_nb (Eras.app_nb hT (.bl (Eras.app_nb hD hS) ?_))
  cases hdr : u.drop p with
  | nil =>
    rcases hSh with rfl | ⟨S', rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨1, S', rfl, one_nb⟩
  | cons d D =>
    refine Or.inr ⟨d, D ++ S, rfl, ?_⟩
    rw [hdr] at hD
    exact hD d (List.mem_cons_self ..)

theorem storeOf_head (x : List Bool) (pos : List Nat) (cur : Nat) : ∃ S', storeOf x pos cur = 1 :: S' := by
  unfold storeOf cfg
  rcases ucs_shape (uOf x) (pos.drop (cur + 1)) with h | ⟨S, h⟩
  · exact ⟨(uOf x).take (pos.getD cur 0) ++ 0 :: ((uOf x).drop (pos.getD cur 0) ++ ucs (uOf x) (pos.take cur)),
      by rw [h]; simp [uc]⟩
  · rw [h]; exact ⟨_, rfl⟩

theorem Eras_storeOf (x : List Bool) (pos : List Nat) (cur : Nat) : Eras (storeOf x pos cur) := by
  unfold storeOf cfg
  have hu := Bits.uOf x
  have hSR : NoB (ucs (uOf x) (pos.take cur)) := NoB.ucs hu _
  rw [List.append_assoc]
  refine Eras.app_nb (NoB.ucs hu _) (Eras_uc0 hu _ (Eras.of_noB hSR) ?_)
  rcases ucs_shape (uOf x) (pos.take cur) with h | ⟨S, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨S, h⟩

/-- The gap and the storage after the fuel. -/
theorem Eras_gap_store {F : List Nat} (hF : NoB F) (x : List Bool) (pos : List Nat) (cur : Nat) :
    Eras (F ++ 0 :: storeOf x pos cur) := by
  refine Eras.app_nb hF (.bl (Eras_storeOf x pos cur) (Or.inr ?_))
  obtain ⟨S', h⟩ := storeOf_head x pos cur
  exact ⟨1, S', h, one_nb⟩

end ZP.MH
