module

public import ZP.MMSetupGlue
public import ZP.MMRowsAll
public import ZP.MMDry2
public import ZP.MMBRow
public import ZP.MMRSLoop
public import ZP.MMFetch2

@[expose] public section

/-! The dry first row: `m` cycles, each moves one `B` row past `P`. -/

namespace ZP.Mul.MM

open ZP

theorem zipWith_jc_one : ∀ (V C : List Nat), V.length = C.length → List.zipWith (jc 1) V C = C
  | [], [], _ => rfl
  | v :: V, x :: C, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [zipWith_jc_one V C h]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem dryCycle (m : Nat) (row : List Nat) (hrow : Bits row) (hlen : row.length = m)
    (F0 : List Nat) (hF0 : Bits F0) (Bd : List Nat) (hBd : Bits Bd) (t : Nat) (Y : List Nat) (hY : Bits Y)
    (hZY : t + 1 + Y.length = m) (R0 : List Nat) (hR : Sym4 R0) :
    zmmLogic.Reach (hd QMM.FA (F0 ++ row.reverse) (0 :: Bd ++ 1 :: (List.replicate t 2 ++ 3 :: Y) ++ 0 :: 1 :: R0))
      (hd QMM.FA F0 (0 :: (row.reverse ++ Bd) ++ 1 :: (List.replicate (t + 1) 2 ++ Y) ++ 0 :: 1 :: R0)) := by
  obtain ⟨v, Vt, rfl⟩ : ∃ v Vt, row = v :: Vt := by
    cases row with
    | nil => simp at hlen; omega
    | cons v Vt => exact ⟨v, Vt, rfl⟩
  have hv : v ∈ bits := hrow.head
  have hVt : Bits Vt := hrow.tail
  have hlen' : Vt.length + 1 = m := by simpa using hlen
  have h1 := dryBad (F0 ++ Vt.reverse) Bd (List.replicate t 2) Y R0 v (hF0.app hVt.rev) hv hBd
    (fun a ha => List.eq_of_mem_replicate ha) hY hR
  -- the accumulator
  have hacc : (List.replicate t 2 ++ 2 :: Y) ≠ [] := by simp
  obtain ⟨acc0, x, hacc0⟩ := List.eq_nil_or_concat (List.replicate t 2 ++ 2 :: Y) |>.resolve_left hacc
  rw [List.concat_eq_append] at hacc0
  have haccB : Bits (List.replicate t 2 ++ 2 :: Y) := by
    refine Bits.app (fun a ha => ?_) (Bits.cons (by simp [bits]) hY)
    rw [List.eq_of_mem_replicate ha]; simp [bits]
  rw [hacc0] at haccB
  have hacc0B : Bits acc0 := fun a ha => haccB a (by simp [ha])
  have hxB : x ∈ bits := haccB x (by simp)
  have hlenacc : acc0.length = Vt.length := by
    have := congrArg List.length hacc0
    simp at this; omega
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have h1u : (1 : Nat) ∈ ALL := by simp [ALL]
  have hSym : Sym4 (F0 ++ 0 :: (Vt.reverse ++ v :: Bd ++ [1])) := by
    simp [sym4_app_iff, sym4_cons_iff, h0, h1u, hF0.sym4, hVt.rev.sym4, bits_all hv, hBd.sym4]
  have h2 := bRow 1 (Or.inl rfl) R0 hR Vt acc0.reverse (by simpa using hlenacc.symm) hVt hacc0B.rev v x hv hxB F0 Bd [] hF0.sym4 hBd Bits.nil
  have hstart : hdR QMM.J1 (F0 ++ Vt.reverse) (v :: 0 :: (Bd ++ 1 :: (acc0.reverse.reverse ++ [x] ++ 0 :: ([] ++ 1 :: R0)))) =
      hd QMM.J1 (F0 ++ Vt.reverse ++ [v]) (0 :: Bd ++ 1 :: (List.replicate t 2 ++ 2 :: (Y ++ 0 :: 1 :: R0))) := by
    rw [hd_snoc]
    simp only [List.reverse_reverse, List.nil_append]
    have : List.replicate t 2 ++ 2 :: (Y ++ 0 :: 1 :: R0) = (acc0 ++ [x]) ++ 0 :: 1 :: R0 := by
      rw [← hacc0]; simp
    rw [this]
    simp
  have hA : zmmLogic.Reach (hd QMM.FA (F0 ++ (v :: Vt).reverse) (0 :: Bd ++ 1 :: (List.replicate t 2 ++ 3 :: Y) ++ 0 :: 1 :: R0))
      (hdR QMM.J1 (F0 ++ Vt.reverse) (v :: 0 :: (Bd ++ 1 :: (acc0.reverse.reverse ++ [x] ++ 0 :: ([] ++ 1 :: R0))))) :=
    h1.of_eq (by simp) (by have := hstart; simp only [List.cons_append, List.append_assoc, List.nil_append, List.reverse_reverse] at this ⊢; exact this.symm)
  have hzw : (List.zipWith (jc 1) (v :: Vt) (x :: acc0.reverse)).reverse = acc0 ++ [x] := by
    rw [zipWith_jc_one _ _ (by simp [hlenacc])]
    simp
  have hAcc : Bits (acc0 ++ [x]) := hacc0B.snoc hxB
  have hacc1 : acc0 ++ [x] = List.replicate (t + 1) 2 ++ Y := by
    rw [← hacc0]; simp [List.replicate_succ']
  have h3 := rsLoop (acc0 ++ [x]) hAcc (F0 ++ 0 :: (Vt.reverse ++ v :: Bd ++ [1])) hSym R0 hR
  have h4 := toFA F0 (Vt.reverse ++ v :: Bd) (acc0 ++ [x]) R0 hF0.sym4 (hVt.rev.app (Bits.cons hv hBd)) hAcc hR
  have h2' := h2.of_eq rfl (show _ = hdR QMM.RS1 (F0 ++ 0 :: (Vt.reverse ++ v :: Bd ++ [1])) (0 :: ((acc0 ++ [x]) ++ 1 :: R0)) by
    rw [hzw]; simp)
  have h34 := h3.trans (h4.of_eq (by simp) rfl)
  have := hA.trans (h2'.trans h34)
  rw [hacc1] at this
  exact this.of_eq (by simp) (by simp)


/-- All `m` dry cycles: the `B` rows `Rrem` move past `P`, one ruler cell is marked per row. -/
theorem dryRows (m : Nat) : ∀ (Rrem Done : List (List Nat)) (F0 : List Nat) (t : Nat),
    (∀ r ∈ Rrem, Bits r ∧ r.length = m) → Bits F0 → (∀ r ∈ Done, Bits r) → Rrem.length + t = m →
    ∀ R0, Sym4 R0 →
    zmmLogic.Reach (hd QMM.FA (F0 ++ stor Rrem) (0 :: stor Done ++ 1 :: (List.replicate t 2 ++ List.replicate Rrem.length 3) ++ 0 :: 1 :: R0))
      (hd QMM.FA F0 (0 :: stor (Done ++ Rrem) ++ 1 :: List.replicate m 2 ++ 0 :: 1 :: R0))
  | [], Done, F0, t, _, _, _, ht, R0, _ => by
    have : t = m := by simpa using ht
    subst this
    simp [stor]
    exact LTM.Reach.refl _ _
  | row :: Rest, Done, F0, t, hR, hF0, hD, ht, R0, hR0 => by
    have hrow := hR row (by simp)
    have hRest : ∀ r ∈ Rest, Bits r ∧ r.length = m := fun r hr => hR r (by simp [hr])
    have hBd := bits_stor Done hD
    have hRB : Bits (stor Rest) := bits_stor Rest (fun r hr => (hRest r hr).1)
    have hlt : Rest.length + 1 + t = m := by simpa using ht
    have h1 := dryCycle m row hrow.1 hrow.2 (F0 ++ stor Rest) (hF0.app hRB) (stor Done) hBd t
      (List.replicate Rest.length 3) (fun a ha => by rw [List.eq_of_mem_replicate ha]; simp [bits])
      (by simp; omega) R0 hR0
    have h2 := dryRows m Rest (Done ++ [row]) F0 (t + 1) hRest hF0
      (fun r hr => by
        rcases List.mem_append.mp hr with h | h
        · exact hD r h
        · simp at h; subst h; exact hrow.1)
      (by simp at ht ⊢; omega) R0 hR0
    have e1 : stor Done ++ [] = stor Done := by simp
    have e2 : stor (Done ++ [row]) = row.reverse ++ stor Done := by
      rw [stor_append]; simp [stor]
    have e3 : Done ++ row :: Rest = Done ++ [row] ++ Rest := by simp
    rw [e3]
    have h1' : zmmLogic.Reach (hd QMM.FA (F0 ++ stor (row :: Rest))
        (0 :: stor Done ++ 1 :: (List.replicate t 2 ++ List.replicate (row :: Rest).length 3) ++ 0 :: 1 :: R0))
        (hd QMM.FA (F0 ++ stor Rest)
        (0 :: stor (Done ++ [row]) ++ 1 :: (List.replicate (t + 1) 2 ++ List.replicate Rest.length 3) ++ 0 :: 1 :: R0)) :=
      h1.of_eq (by simp [stor, List.replicate_succ]) (by rw [e2])
    exact h1'.trans h2

theorem dryFinE (Wr Bd Os Rest : List Nat) (b x : Nat) (Wt : List Nat) (e m : Nat) (he : e = 0 ∨ e = 1)
    (hWe : Wr ++ [b] = x :: Wt) (hWr : Bits Wr) (hbb : b ∈ bits) (hBd : Bits Bd) (hOs : Bits Os)
    (hRest : Sym4 Rest) :
    zmmLogic.Reach (hd QMM.FA (Wr ++ [b]) (0 :: Bd ++ 1 :: List.replicate m 2 ++ 0 :: 1 :: (Os ++ e :: Rest)))
      (hdR QMM.RS1 (Wr ++ [b] ++ 1 :: Bd ++ [0, 1]) (0 :: ((Os.reverse ++ List.replicate m 2).take m).reverse ++ [] ++
        1 :: (Os.take (Os.length - m) ++ List.replicate (min m Os.length) 0 ++ e :: Rest))) := by
  have hOe : Sym4 (Os ++ e :: Rest) := by
    refine Sym4.app hOs.sym4 (Sym4.cons ?_ hRest)
    rcases he with rfl | rfl <;> simp [ALL]
  have s0 := dryOK Wr Bd (List.replicate m 2) (Os ++ e :: Rest) b hWr hbb hBd
    (fun a ha => List.eq_of_mem_replicate ha) hOe
  have hA : Sym4 ([0] ++ (Wr ++ [b]) ++ [0] ++ Bd ++ [1]) := by
    have hWb4 : Sym4 (Wr ++ [b]) := by
      rw [sym4_app_iff]
      refine ⟨hWr.sym4, Sym4.cons ?_ Sym4.nil⟩
      rcases mem_bits hbb with rfl | rfl <;> simp [ALL]
    have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
    have h1 : (1 : Nat) ∈ ALL := by simp [ALL]
    have z : Sym4 [0] := Sym4.cons h0 Sym4.nil
    exact Sym4.app (Sym4.app (Sym4.app (Sym4.app z hWb4) z) hBd.sym4) (Sym4.cons h1 Sym4.nil)
  have s1 := qPass _ hA m [] Os Rest e he Bits.nil hOs hRest
  have hR1 : Sym4 (0 :: ((Os.reverse ++ List.replicate m 2).take m).reverse ++ [] ++
      1 :: (Os.take (Os.length - m) ++ List.replicate (min m Os.length) 0 ++ e :: Rest)) := by
    have h2 : ∀ a ∈ ((Os.reverse ++ List.replicate m 2).take m).reverse, a ∈ ALL := by
      intro a ha
      rw [List.mem_reverse] at ha
      have := List.mem_of_mem_take ha
      rw [List.mem_append, List.mem_reverse] at this
      rcases this with h | h
      · exact hOs.sym4 a h
      · rw [List.eq_of_mem_replicate h]; simp [ALL]
    have h3 : ∀ a ∈ Os.take (Os.length - m), a ∈ ALL := fun a ha => hOs.sym4 a (List.mem_of_mem_take ha)
    have h4 : ∀ a ∈ List.replicate (min m Os.length) 0, a ∈ ALL := fun a ha => by
      rw [List.eq_of_mem_replicate ha]; simp [ALL]
    have h5 : e ∈ ALL := by rcases he with rfl | rfl <;> simp [ALL]
    have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
    have h1 : (1 : Nat) ∈ ALL := by simp [ALL]
    simp [sym4_app_iff, sym4_cons_iff, h0, h1, h5]
    exact ⟨h2, h3, h4, hRest⟩
  have s2 := dryN Wr Bd _ b x Wt hWe hWr hbb hBd hR1
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at s0 s1 s2 ⊢
  exact s0.trans (s1.trans s2)


end ZP.Mul.MM
