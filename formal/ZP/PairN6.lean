module

public import ZP.PairN5

@[expose] public section

/-! # The pair lemma of the NTT machine, part 6: the column loop -/

namespace ZP.N

open ZP ZP.G


theorem blankL_DU1 (A : List Nat) (hA : ∀ y ∈ A, y ∈ U4) (x : Nat) (hx : x = 1 ∨ x = 2 ∨ x = 3) :
    znttLogic.Reach
      (hdR QN.DU1 (A ++ [x])
        ([]))
      (hd QN.RFL (A ++ [x])
        ([0])) := by
  have hV : Valid [U4] [A] :=
    Valid.cons hA (Valid.nil _)
  rcases hx with rfl | rfl | rfl
  · exact checkFT (env := [A]) (E := []) (k := 20) hV trivial
      (ls := [.blk 0 .id, .sym 1]) (rs := [])
      (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 0])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [A]) (E := []) (k := 20) hV trivial
      (ls := [.blk 0 .id, .sym 2]) (rs := [])
      (ls' := [.blk 0 .id, .sym 2]) (rs' := [.sym 0])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [A]) (E := []) (k := 20) hV trivial
      (ls := [.blk 0 .id, .sym 3]) (rs := [])
      (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 0])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem DU1_RFL (A1 B : List Nat) (hA : ∀ y ∈ A1, y ∈ U4) (hB : NoB B) (hne : B ≠ []) :
    znttLogic.Reach (hdR QN.DU1 (A1 ++ B) []) (hd QN.RFL (A1 ++ B) [0]) := by
  obtain ⟨B0, x, rfl⟩ := List.eq_nil_or_concat B |>.resolve_left hne
  simp only [List.concat_eq_append] at *
  have hx : x = 1 ∨ x = 2 ∨ x = 3 := by
    have := hB x (by simp)
    simpa [NB] using this
  have hA0 : ∀ y ∈ A1 ++ B0, y ∈ U4 := fun y hy => by
    rcases List.mem_append.1 hy with h | h
    · exact hA y h
    · exact nb_u4 (hB y (by simp [h]))
  have := blankL_DU1 (A1 ++ B0) hA0 x hx
  simpa [List.append_assoc] using this

theorem blankL_DN0 (A : List Nat) (hA : ∀ y ∈ A, y ∈ U4) (x : Nat) (hx : x = 1 ∨ x = 2 ∨ x = 3) :
    znttLogic.Reach
      (hdR QN.DN0 (A ++ [x])
        ([]))
      (hd QN.RFL (A ++ [x])
        ([0])) := by
  have hV : Valid [U4] [A] :=
    Valid.cons hA (Valid.nil _)
  rcases hx with rfl | rfl | rfl
  · exact checkFT (env := [A]) (E := []) (k := 20) hV trivial
      (ls := [.blk 0 .id, .sym 1]) (rs := [])
      (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 0])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [A]) (E := []) (k := 20) hV trivial
      (ls := [.blk 0 .id, .sym 2]) (rs := [])
      (ls' := [.blk 0 .id, .sym 2]) (rs' := [.sym 0])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [A]) (E := []) (k := 20) hV trivial
      (ls := [.blk 0 .id, .sym 3]) (rs := [])
      (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 0])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem DN0_RFL (A1 B : List Nat) (hA : ∀ y ∈ A1, y ∈ U4) (hB : NoB B) (hne : B ≠ []) :
    znttLogic.Reach (hdR QN.DN0 (A1 ++ B) []) (hd QN.RFL (A1 ++ B) [0]) := by
  obtain ⟨B0, x, rfl⟩ := List.eq_nil_or_concat B |>.resolve_left hne
  simp only [List.concat_eq_append] at *
  have hx : x = 1 ∨ x = 2 ∨ x = 3 := by
    have := hB x (by simp)
    simpa [NB] using this
  have hA0 : ∀ y ∈ A1 ++ B0, y ∈ U4 := fun y hy => by
    rcases List.mem_append.1 hy with h | h
    · exact hA y h
    · exact nb_u4 (hB y (by simp [h]))
  have := blankL_DN0 (A1 ++ B0) hA0 x hx
  simpa [List.append_assoc] using this

theorem blankL_BS0 (A : List Nat) (hA : ∀ y ∈ A, y ∈ U4) (x : Nat) (hx : x = 1 ∨ x = 2 ∨ x = 3) :
    znttLogic.Reach
      (hdR QN.BS0 (A ++ [x])
        ([]))
      (hd QN.RFL (A ++ [x])
        ([0])) := by
  have hV : Valid [U4] [A] :=
    Valid.cons hA (Valid.nil _)
  rcases hx with rfl | rfl | rfl
  · exact checkFT (env := [A]) (E := []) (k := 20) hV trivial
      (ls := [.blk 0 .id, .sym 1]) (rs := [])
      (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 0])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [A]) (E := []) (k := 20) hV trivial
      (ls := [.blk 0 .id, .sym 2]) (rs := [])
      (ls' := [.blk 0 .id, .sym 2]) (rs' := [.sym 0])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [A]) (E := []) (k := 20) hV trivial
      (ls := [.blk 0 .id, .sym 3]) (rs := [])
      (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 0])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem BS0_RFL (A1 B : List Nat) (hA : ∀ y ∈ A1, y ∈ U4) (hB : NoB B) (hne : B ≠ []) :
    znttLogic.Reach (hdR QN.BS0 (A1 ++ B) []) (hd QN.RFL (A1 ++ B) [0]) := by
  obtain ⟨B0, x, rfl⟩ := List.eq_nil_or_concat B |>.resolve_left hne
  simp only [List.concat_eq_append] at *
  have hx : x = 1 ∨ x = 2 ∨ x = 3 := by
    have := hB x (by simp)
    simpa [NB] using this
  have hA0 : ∀ y ∈ A1 ++ B0, y ∈ U4 := fun y hy => by
    rcases List.mem_append.1 hy with h | h
    · exact hA y h
    · exact nb_u4 (hB y (by simp [h]))
  have := blankL_BS0 (A1 ++ B0) hA0 x hx
  simpa [List.append_assoc] using this

theorem blankL_CU1 (A : List Nat) (hA : ∀ y ∈ A, y ∈ U4) (x : Nat) (hx : x = 1 ∨ x = 2 ∨ x = 3) :
    znttLogic.Reach
      (hdR QN.CU1 (A ++ [x])
        ([]))
      (hd QN.RFL (A ++ [x])
        ([0])) := by
  have hV : Valid [U4] [A] :=
    Valid.cons hA (Valid.nil _)
  rcases hx with rfl | rfl | rfl
  · exact checkFT (env := [A]) (E := []) (k := 20) hV trivial
      (ls := [.blk 0 .id, .sym 1]) (rs := [])
      (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 0])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [A]) (E := []) (k := 20) hV trivial
      (ls := [.blk 0 .id, .sym 2]) (rs := [])
      (ls' := [.blk 0 .id, .sym 2]) (rs' := [.sym 0])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [A]) (E := []) (k := 20) hV trivial
      (ls := [.blk 0 .id, .sym 3]) (rs := [])
      (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 0])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem CU1_RFL (A1 B : List Nat) (hA : ∀ y ∈ A1, y ∈ U4) (hB : NoB B) (hne : B ≠ []) :
    znttLogic.Reach (hdR QN.CU1 (A1 ++ B) []) (hd QN.RFL (A1 ++ B) [0]) := by
  obtain ⟨B0, x, rfl⟩ := List.eq_nil_or_concat B |>.resolve_left hne
  simp only [List.concat_eq_append] at *
  have hx : x = 1 ∨ x = 2 ∨ x = 3 := by
    have := hB x (by simp)
    simpa [NB] using this
  have hA0 : ∀ y ∈ A1 ++ B0, y ∈ U4 := fun y hy => by
    rcases List.mem_append.1 hy with h | h
    · exact hA y h
    · exact nb_u4 (hB y (by simp [h]))
  have := blankL_CU1 (A1 ++ B0) hA0 x hx
  simpa [List.append_assoc] using this

theorem blankL_LN0 (A : List Nat) (hA : ∀ y ∈ A, y ∈ U4) (x : Nat) (hx : x = 1 ∨ x = 2 ∨ x = 3) :
    znttLogic.Reach
      (hdR QN.LN0 (A ++ [x])
        ([]))
      (hd QN.RFL (A ++ [x])
        ([0])) := by
  have hV : Valid [U4] [A] :=
    Valid.cons hA (Valid.nil _)
  rcases hx with rfl | rfl | rfl
  · exact checkFT (env := [A]) (E := []) (k := 20) hV trivial
      (ls := [.blk 0 .id, .sym 1]) (rs := [])
      (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 0])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [A]) (E := []) (k := 20) hV trivial
      (ls := [.blk 0 .id, .sym 2]) (rs := [])
      (ls' := [.blk 0 .id, .sym 2]) (rs' := [.sym 0])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [A]) (E := []) (k := 20) hV trivial
      (ls := [.blk 0 .id, .sym 3]) (rs := [])
      (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 0])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem LN0_RFL (A1 B : List Nat) (hA : ∀ y ∈ A1, y ∈ U4) (hB : NoB B) (hne : B ≠ []) :
    znttLogic.Reach (hdR QN.LN0 (A1 ++ B) []) (hd QN.RFL (A1 ++ B) [0]) := by
  obtain ⟨B0, x, rfl⟩ := List.eq_nil_or_concat B |>.resolve_left hne
  simp only [List.concat_eq_append] at *
  have hx : x = 1 ∨ x = 2 ∨ x = 3 := by
    have := hB x (by simp)
    simpa [NB] using this
  have hA0 : ∀ y ∈ A1 ++ B0, y ∈ U4 := fun y hy => by
    rcases List.mem_append.1 hy with h | h
    · exact hA y h
    · exact nb_u4 (hB y (by simp [h]))
  have := blankL_LN0 (A1 ++ B0) hA0 x hx
  simpa [List.append_assoc] using this

theorem blankL_CA4 (A : List Nat) (hA : ∀ y ∈ A, y ∈ U4) (x : Nat) (hx : x = 1 ∨ x = 2 ∨ x = 3) :
    znttLogic.Reach
      (hdR QN.CA4 (A ++ [x])
        ([]))
      (hd QN.PE0 (A ++ [x])
        ([0])) := by
  have hV : Valid [U4] [A] :=
    Valid.cons hA (Valid.nil _)
  rcases hx with rfl | rfl | rfl
  · exact checkFT (env := [A]) (E := []) (k := 20) hV trivial
      (ls := [.blk 0 .id, .sym 1]) (rs := [])
      (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 0])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [A]) (E := []) (k := 20) hV trivial
      (ls := [.blk 0 .id, .sym 2]) (rs := [])
      (ls' := [.blk 0 .id, .sym 2]) (rs' := [.sym 0])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [A]) (E := []) (k := 20) hV trivial
      (ls := [.blk 0 .id, .sym 3]) (rs := [])
      (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 0])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem CA4_PE0 (A1 B : List Nat) (hA : ∀ y ∈ A1, y ∈ U4) (hB : NoB B) (hne : B ≠ []) :
    znttLogic.Reach (hdR QN.CA4 (A1 ++ B) []) (hd QN.PE0 (A1 ++ B) [0]) := by
  obtain ⟨B0, x, rfl⟩ := List.eq_nil_or_concat B |>.resolve_left hne
  simp only [List.concat_eq_append] at *
  have hx : x = 1 ∨ x = 2 ∨ x = 3 := by
    have := hB x (by simp)
    simpa [NB] using this
  have hA0 : ∀ y ∈ A1 ++ B0, y ∈ U4 := fun y hy => by
    rcases List.mem_append.1 hy with h | h
    · exact hA y h
    · exact nb_u4 (hB y (by simp [h]))
  have := blankL_CA4 (A1 ++ B0) hA0 x hx
  simpa [List.append_assoc] using this

theorem decMid0 (A Ba Be Bz : List Nat) (a : Nat) (hA : ∀ x ∈ A, x ∈ U4) (hBa : ∀ x ∈ Ba, x ∈ bits) (hBe : ∀ x ∈ Be, x ∈ bits) (hBz : ∀ x ∈ Bz, x ∈ bits) (Hdr rest : List Nat) (hHdr : ∀ x ∈ Hdr, x ∈ bits) (hrest : NoB rest) :
    znttLogic.Reach
      (hdR QN.DAc (A)
        (Ba ++ [1] ++ Be ++ [1] ++ Bz ++ [1] ++ (List.replicate a 2) ++ [3, 1, 1] ++ Hdr ++ [1] ++ rest))
      (hdR QN.DAc (A ++ Ba ++ [1] ++ Be ++ [1] ++ Bz ++ [1] ++ (List.replicate a 2) ++ [3, 1, 1] ++ Hdr ++ [1])
        (rest)) := by
  have hV : Valid [U4, bits, bits, bits, Mk, bits, NB] [A, Ba, Be, Bz, List.replicate a 2, Hdr, rest] :=
    Valid.cons hA (Valid.cons hBa (Valid.cons hBe (Valid.cons hBz (Valid.cons (rep2_mk a) (Valid.cons hHdr (Valid.cons hrest (Valid.nil _)))))))
  exact checkFF (env := [A, Ba, Be, Bz, List.replicate a 2, Hdr, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .sym 1, .sym 1, .blk 5 .id, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .sym 1, .sym 1, .blk 5 .id, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem decMid2 (A Ba Be Bz : List Nat) (a : Nat) (hA : ∀ x ∈ A, x ∈ U4) (hBa : ∀ x ∈ Ba, x ∈ bits) (hBe : ∀ x ∈ Be, x ∈ bits) (hBz : ∀ x ∈ Bz, x ∈ bits) (Y : List Nat) (hY : ∀ x ∈ Y, x ∈ bits) (Hdr rest : List Nat) (hHdr : ∀ x ∈ Hdr, x ∈ bits) (hrest : NoB rest) :
    znttLogic.Reach
      (hdR QN.DAc (A)
        (Ba ++ [1] ++ Be ++ [1] ++ Bz ++ [1] ++ (List.replicate a 2) ++ [3, 2] ++ Y ++ [1, 1] ++ Hdr ++ [1] ++ rest))
      (hdR QN.DAc (A ++ Ba ++ [1] ++ Be ++ [1] ++ Bz ++ [1] ++ (List.replicate a 2) ++ [3, 2] ++ Y ++ [1, 1] ++ Hdr ++ [1])
        (rest)) := by
  have hV : Valid [U4, bits, bits, bits, Mk, bits, bits, NB] [A, Ba, Be, Bz, List.replicate a 2, Y, Hdr, rest] :=
    Valid.cons hA (Valid.cons hBa (Valid.cons hBe (Valid.cons hBz (Valid.cons (rep2_mk a) (Valid.cons hY (Valid.cons hHdr (Valid.cons hrest (Valid.nil _))))))))
  exact checkFF (env := [A, Ba, Be, Bz, List.replicate a 2, Y, Hdr, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .sym 2, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id, .sym 1, .blk 7 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .sym 2, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id, .sym 1]) (rs' := [.blk 7 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem decMid3 (A Ba Be Bz : List Nat) (a : Nat) (hA : ∀ x ∈ A, x ∈ U4) (hBa : ∀ x ∈ Ba, x ∈ bits) (hBe : ∀ x ∈ Be, x ∈ bits) (hBz : ∀ x ∈ Bz, x ∈ bits) (Y : List Nat) (hY : ∀ x ∈ Y, x ∈ bits) (Hdr rest : List Nat) (hHdr : ∀ x ∈ Hdr, x ∈ bits) (hrest : NoB rest) :
    znttLogic.Reach
      (hdR QN.DAc (A)
        (Ba ++ [1] ++ Be ++ [1] ++ Bz ++ [1] ++ (List.replicate a 2) ++ [3, 3] ++ Y ++ [1, 1] ++ Hdr ++ [1] ++ rest))
      (hdR QN.DAc (A ++ Ba ++ [1] ++ Be ++ [1] ++ Bz ++ [1] ++ (List.replicate a 2) ++ [2, 3] ++ Y ++ [1, 1] ++ Hdr ++ [1])
        (rest)) := by
  have hV : Valid [U4, bits, bits, bits, Mk, bits, bits, NB] [A, Ba, Be, Bz, List.replicate a 2, Y, Hdr, rest] :=
    Valid.cons hA (Valid.cons hBa (Valid.cons hBe (Valid.cons hBz (Valid.cons (rep2_mk a) (Valid.cons hY (Valid.cons hHdr (Valid.cons hrest (Valid.nil _))))))))
  exact checkFF (env := [A, Ba, Be, Bz, List.replicate a 2, Y, Hdr, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id, .sym 1, .blk 7 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 2, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id, .sym 1]) (rs' := [.blk 7 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem decLast0 (A Ba Be Bz : List Nat) (a : Nat) (hA : ∀ x ∈ A, x ∈ U4) (hBa : ∀ x ∈ Ba, x ∈ bits) (hBe : ∀ x ∈ Be, x ∈ bits) (hBz : ∀ x ∈ Bz, x ∈ bits) :
    znttLogic.Reach
      (hdR QN.DAc (A)
        (Ba ++ [1] ++ Be ++ [1] ++ Bz ++ [1] ++ (List.replicate a 2) ++ [3]))
      (hdR QN.DU1 (A ++ Ba ++ [1] ++ Be ++ [1] ++ Bz ++ [1] ++ (List.replicate a 2) ++ [3])
        ([])) := by
  have hV : Valid [U4, bits, bits, bits, Mk] [A, Ba, Be, Bz, List.replicate a 2] :=
    Valid.cons hA (Valid.cons hBa (Valid.cons hBe (Valid.cons hBz (Valid.cons (rep2_mk a) (Valid.nil _)))))
  exact checkFF (env := [A, Ba, Be, Bz, List.replicate a 2]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem decLast2 (A Ba Be Bz : List Nat) (a : Nat) (hA : ∀ x ∈ A, x ∈ U4) (hBa : ∀ x ∈ Ba, x ∈ bits) (hBe : ∀ x ∈ Be, x ∈ bits) (hBz : ∀ x ∈ Bz, x ∈ bits) (Y : List Nat) (hY : ∀ x ∈ Y, x ∈ bits) :
    znttLogic.Reach
      (hdR QN.DAc (A)
        (Ba ++ [1] ++ Be ++ [1] ++ Bz ++ [1] ++ (List.replicate a 2) ++ [3, 2] ++ Y))
      (hdR QN.DN0 (A ++ Ba ++ [1] ++ Be ++ [1] ++ Bz ++ [1] ++ (List.replicate a 2) ++ [3, 2] ++ Y)
        ([])) := by
  have hV : Valid [U4, bits, bits, bits, Mk, bits] [A, Ba, Be, Bz, List.replicate a 2, Y] :=
    Valid.cons hA (Valid.cons hBa (Valid.cons hBe (Valid.cons hBz (Valid.cons (rep2_mk a) (Valid.cons hY (Valid.nil _))))))
  exact checkFF (env := [A, Ba, Be, Bz, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .sym 2, .blk 5 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .sym 2, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem decLast3 (A Ba Be Bz : List Nat) (a : Nat) (hA : ∀ x ∈ A, x ∈ U4) (hBa : ∀ x ∈ Ba, x ∈ bits) (hBe : ∀ x ∈ Be, x ∈ bits) (hBz : ∀ x ∈ Bz, x ∈ bits) (Y : List Nat) (hY : ∀ x ∈ Y, x ∈ bits) :
    znttLogic.Reach
      (hdR QN.DAc (A)
        (Ba ++ [1] ++ Be ++ [1] ++ Bz ++ [1] ++ (List.replicate a 2) ++ [3, 3] ++ Y))
      (hdR QN.DN0 (A ++ Ba ++ [1] ++ Be ++ [1] ++ Bz ++ [1] ++ (List.replicate a 2) ++ [2, 3] ++ Y)
        ([])) := by
  have hV : Valid [U4, bits, bits, bits, Mk, bits] [A, Ba, Be, Bz, List.replicate a 2, Y] :=
    Valid.cons hA (Valid.cons hBa (Valid.cons hBe (Valid.cons hBz (Valid.cons (rep2_mk a) (Valid.cons hY (Valid.nil _))))))
  exact checkFF (env := [A, Ba, Be, Bz, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 2, .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-! ## The decrement sweep -/

/-- One decrement of a pointer: the first unmarked `1` is marked unless it is the last one. -/
def decU : List Nat → List Nat
  | [] => []
  | x :: l =>
    if x = 2 then 2 :: decU l
    else if x = 3 then (match l with | 3 :: l' => 2 :: 3 :: l' | _ => x :: l)
    else x :: l

theorem decU_nil (a : Nat) : decU (List.replicate a 2 ++ [3]) = List.replicate a 2 ++ [3] := by
  induction a with
  | zero => rfl
  | succ a ih => simp [List.replicate_succ, decU, ih]

theorem decU_two (a : Nat) (Y : List Nat) : decU (List.replicate a 2 ++ 3 :: 2 :: Y) = List.replicate a 2 ++ 3 :: 2 :: Y := by
  induction a with
  | zero => rfl
  | succ a ih => simp [List.replicate_succ, decU, ih]

theorem decU_three (a : Nat) (Y : List Nat) : decU (List.replicate a 2 ++ 3 :: 3 :: Y) = List.replicate a 2 ++ 2 :: 3 :: Y := by
  induction a with
  | zero => rfl
  | succ a ih => simp [List.replicate_succ, decU, ih]

def ER.dec (r : ER) : ER := { r with u := decU r.u }

/-- The shape needed by the decrement sweep. -/
structure ER.decOk (r : ER) : Prop where
  ok : r.ok
  uShape : ∃ a Y, r.u = List.replicate a 2 ++ 3 :: Y

theorem decU_mem (l : List Nat) : ∀ x ∈ decU l, x = 2 ∨ x ∈ l := by
  induction l with
  | nil => intro x hx; simp [decU] at hx
  | cons y l ih =>
    intro x hx
    by_cases hy : y = 2
    · subst hy
      simp only [decU, if_true, List.mem_cons] at hx
      rcases hx with rfl | hx
      · left; rfl
      · rcases ih x hx with h | h
        · left; exact h
        · right; simp [h]
    · by_cases h3 : y = 3
      · subst h3
        cases l with
        | nil => right; simpa [decU] using hx
        | cons z l' =>
          by_cases hz : z = 3
          · subst hz
            simp [decU] at hx
            rcases hx with h | h | h
            · left; exact h
            · right; simp [h]
            · right; simp [h]
          · simp [decU, hz] at hx
            right; simpa using hx
      · simp [decU, hy, h3] at hx
        right; simpa using hx

theorem decU_bits (l : List Nat) (h : Bits l) : Bits (decU l) := by
  intro x hx
  rcases decU_mem l x hx with rfl | h'
  · simp [bits]
  · exact h x h'

theorem ER.dec_ok (r : ER) (h : r.ok) : r.dec.ok where
  f := h.f
  o := h.o
  pf := h.pf
  acc := h.acc
  E := h.E
  z := h.z
  u := decU_bits _ h.u

theorem bits_cases (Y : List Nat) (hY : Bits Y) :
    Y = [] ∨ (∃ Y', Y = 2 :: Y' ∧ Bits Y') ∨ (∃ Y', Y = 3 :: Y' ∧ Bits Y') := by
  cases Y with
  | nil => exact Or.inl rfl
  | cons y Y' =>
    have hy : y ∈ bits := hY y (by simp)
    have hY' : Bits Y' := fun x hx => hY x (by simp [hx])
    simp only [bits, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact Or.inr (Or.inl ⟨Y', rfl, hY'⟩)
    · exact Or.inr (Or.inr ⟨Y', rfl, hY'⟩)

theorem ER.u_parts (r : ER) (h : r.decOk) :
    ∃ a Y, r.u = List.replicate a 2 ++ 3 :: Y ∧ Bits Y := by
  obtain ⟨a, Y, hY⟩ := h.uShape
  refine ⟨a, Y, hY, fun x hx => h.ok.u x ?_⟩
  rw [hY]; simp [hx]

theorem hdrA_u4 (A : List Nat) (hA : ∀ x ∈ A, x ∈ U4) (r : ER) (h : r.ok) :
    ∀ x ∈ A ++ [1, 1, r.f, r.o, r.pf, 1], x ∈ U4 := by
  intro x hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hx | hx
  · exact hA x hx
  · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [U4]
    · simp [U4]
    · exact nb_u4 (bits_nb (bits_mem h.f))
    · exact nb_u4 (bits_nb (bits_mem h.o))
    · exact nb_u4 (bits_nb (bits_mem h.pf))
    · simp [U4]

theorem decLastER (A : List Nat) (hA : ∀ x ∈ A, x ∈ U4) (r : ER) (h : r.decOk) :
    znttLogic.Reach
      (hdR QN.DAc (A ++ [1, 1, r.f, r.o, r.pf, 1]) (r.acc ++ [1] ++ r.E ++ [1] ++ r.z ++ [1] ++ r.u))
      (hd QN.RFL (A ++ [1, 1] ++ r.dec.tl) [0]) := by
  obtain ⟨a, Y, hu, hY⟩ := r.u_parts h
  have hA2 : ∀ x ∈ A ++ [1, 1], x ∈ U4 := u4_two A hA
  have hne : r.dec.tl ≠ [] := by simp [ER.tl]
  have hnb : NoB r.dec.tl := r.dec.tl_nb (r.dec_ok h.ok)
  have hA1 := hdrA_u4 A hA r h.ok
  rcases bits_cases Y hY with rfl | ⟨Y', rfl, hY'⟩ | ⟨Y', rfl, hY'⟩
  · have h1 := decLast0 (A ++ [1, 1, r.f, r.o, r.pf, 1]) r.acc r.E r.z a hA1 h.ok.acc h.ok.E h.ok.z
    have h2 := DU1_RFL (A ++ [1, 1]) r.dec.tl hA2 hnb hne
    have h1' : znttLogic.Reach
        (hdR QN.DAc (A ++ [1, 1, r.f, r.o, r.pf, 1]) (r.acc ++ [1] ++ r.E ++ [1] ++ r.z ++ [1] ++ r.u))
        (hdR QN.DU1 (A ++ [1, 1] ++ r.dec.tl) []) := by
      refine h1.of_eq ?_ ?_
      · simp [hu]
      · simp [ER.tl, ER.dec, hu, decU_nil, List.append_assoc]
    exact h1'.trans h2
  · have h1 := decLast2 (A ++ [1, 1, r.f, r.o, r.pf, 1]) r.acc r.E r.z a hA1 h.ok.acc h.ok.E h.ok.z Y' hY'
    have h2 := DN0_RFL (A ++ [1, 1]) r.dec.tl hA2 hnb hne
    have h1' : znttLogic.Reach
        (hdR QN.DAc (A ++ [1, 1, r.f, r.o, r.pf, 1]) (r.acc ++ [1] ++ r.E ++ [1] ++ r.z ++ [1] ++ r.u))
        (hdR QN.DN0 (A ++ [1, 1] ++ r.dec.tl) []) := by
      refine h1.of_eq ?_ ?_
      · simp [hu]
      · simp [ER.tl, ER.dec, hu, decU_two, List.append_assoc]
    exact h1'.trans h2
  · have h1 := decLast3 (A ++ [1, 1, r.f, r.o, r.pf, 1]) r.acc r.E r.z a hA1 h.ok.acc h.ok.E h.ok.z Y' hY'
    have h2 := DN0_RFL (A ++ [1, 1]) r.dec.tl hA2 hnb hne
    have h1' : znttLogic.Reach
        (hdR QN.DAc (A ++ [1, 1, r.f, r.o, r.pf, 1]) (r.acc ++ [1] ++ r.E ++ [1] ++ r.z ++ [1] ++ r.u))
        (hdR QN.DN0 (A ++ [1, 1] ++ r.dec.tl) []) := by
      refine h1.of_eq ?_ ?_
      · simp [hu]
      · simp [ER.tl, ER.dec, hu, decU_three, List.append_assoc]
    exact h1'.trans h2

theorem decMidER (A : List Nat) (hA : ∀ x ∈ A, x ∈ U4) (r : ER) (h : r.decOk) (Hdr rest : List Nat)
    (hHdr : Bits Hdr) (hrest : NoB rest) :
    znttLogic.Reach
      (hdR QN.DAc (A ++ [1, 1, r.f, r.o, r.pf, 1])
        (r.acc ++ [1] ++ r.E ++ [1] ++ r.z ++ [1] ++ r.u ++ [1, 1] ++ Hdr ++ [1] ++ rest))
      (hdR QN.DAc (A ++ [1, 1] ++ r.dec.tl ++ [1, 1] ++ Hdr ++ [1]) rest) := by
  obtain ⟨a, Y, hu, hY⟩ := r.u_parts h
  have hA1 := hdrA_u4 A hA r h.ok
  rcases bits_cases Y hY with rfl | ⟨Y', rfl, hY'⟩ | ⟨Y', rfl, hY'⟩
  · have h1 := decMid0 (A ++ [1, 1, r.f, r.o, r.pf, 1]) r.acc r.E r.z a hA1 h.ok.acc h.ok.E h.ok.z Hdr rest hHdr hrest
    refine h1.of_eq ?_ ?_
    · simp [hu, List.append_assoc]
    · simp [ER.tl, ER.dec, hu, decU_nil, List.append_assoc]
  · have h1 := decMid2 (A ++ [1, 1, r.f, r.o, r.pf, 1]) r.acc r.E r.z a hA1 h.ok.acc h.ok.E h.ok.z Y' hY' Hdr rest hHdr hrest
    refine h1.of_eq ?_ ?_
    · simp [hu, List.append_assoc]
    · simp [ER.tl, ER.dec, hu, decU_two, List.append_assoc]
  · have h1 := decMid3 (A ++ [1, 1, r.f, r.o, r.pf, 1]) r.acc r.E r.z a hA1 h.ok.acc h.ok.E h.ok.z Y' hY' Hdr rest hHdr hrest
    refine h1.of_eq ?_ ?_
    · simp [hu, List.append_assoc]
    · simp [ER.tl, ER.dec, hu, decU_three, List.append_assoc]

theorem hdr_bits (r : ER) (h : r.ok) : Bits [r.f, r.o, r.pf] := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact bits_mem h.f
  · exact bits_mem h.o
  · exact bits_mem h.pf

theorem decLoop : ∀ (L : List ER) (r : ER), r.decOk → (∀ r' ∈ L, r'.decOk) → ∀ (A : List Nat), (∀ x ∈ A, x ∈ U4) →
    znttLogic.Reach
      (hdR QN.DAc (A ++ [1, 1, r.f, r.o, r.pf, 1]) (r.acc ++ [1] ++ r.E ++ [1] ++ r.z ++ [1] ++ r.u ++ eTape L))
      (hd QN.RFL (A ++ eTape ((r :: L).map ER.dec)) [0])
  | [], r, hr, _, A, hA => by
    have := decLastER A hA r hr
    refine this.of_eq ?_ ?_
    · simp [eTape]
    · simp [eTape, List.append_assoc]
  | r' :: L, r, hr, hL, A, hA => by
    have hr' : r'.decOk := hL r' (by simp)
    have hLok : ∀ x ∈ L, x.ok := fun x hx => (hL x (by simp [hx])).ok
    have h1 := decMidER A hA r hr [r'.f, r'.o, r'.pf] (r'.acc ++ [1] ++ r'.E ++ [1] ++ r'.z ++ [1] ++ r'.u ++ eTape L)
      (hdr_bits r' hr'.ok) (by
        have hbn : ∀ l, Bits l → NoB l := fun l hl x hx => bits_nb (hl x hx)
        have hone : NoB [1] := by
          intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; simp [NB]
        exact noB_app (noB_app (noB_app (noB_app (noB_app (noB_app (noB_app (hbn _ hr'.ok.acc) hone) (hbn _ hr'.ok.E)) hone)
          (hbn _ hr'.ok.z)) hone) (hbn _ hr'.ok.u)) (noB_eTape L hLok))
    have h2 := decLoop L r' hr' (fun x hx => hL x (by simp [hx])) (A ++ [1, 1] ++ r.dec.tl) (by
      intro x hx
      simp only [List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact hA x hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> simp [U4]
      · exact u4_of_nb (r.dec.tl_nb (r.dec_ok hr.ok)) x hx)
    have h1' : znttLogic.Reach
        (hdR QN.DAc (A ++ [1, 1, r.f, r.o, r.pf, 1]) (r.acc ++ [1] ++ r.E ++ [1] ++ r.z ++ [1] ++ r.u ++ eTape (r' :: L)))
        (hdR QN.DAc (A ++ [1, 1] ++ r.dec.tl ++ [1, 1, r'.f, r'.o, r'.pf, 1]) (r'.acc ++ [1] ++ r'.E ++ [1] ++ r'.z ++ [1] ++ r'.u ++ eTape L)) := by
      refine h1.of_eq ?_ ?_
      · simp [eTape, ER.tl, List.append_assoc]
      · simp [List.append_assoc]
    refine h1'.trans (h2.of_eq rfl ?_)
    simp [eTape, List.append_assoc]

end ZP.N
