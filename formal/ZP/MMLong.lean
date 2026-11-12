module

public import ZP.MMShort
public import ZP.MMRowsAll

@[expose] public section

/-! The long case (`|w| > m²`): the dry row, then all rows. -/

namespace ZP.Mul.MM

open ZP

theorem drop_rev_eq (Os : List Nat) (m : Nat) : (Os.reverse.drop m).reverse = Os.take (Os.length - m) := by
  rw [List.drop_reverse, List.reverse_reverse]

set_option maxHeartbeats 1000000 in
theorem mainLong (m : Nat) (hm : m ≠ 0) (w : List Nat) (hw : Bits w) (hn : m * m < w.length)
    (Os J sv Y2 : List Nat) (hOs : Bits Os) (hJ : Bits J) (hsv : Bits sv) (hY2 : Sym4 Y2)
    (n : Nat) (hnA : (w.drop (m * m)).length ≤ n * m) :
    (rowsOK m (rowsOf m w m) n (w.drop (m * m)) ((Os.reverse ++ List.replicate m 2).take m) (Os.reverse.drop m) →
      zmmLogic.Reach (hd QMM.FA w.reverse (0 :: [] ++ 1 :: List.replicate m 3 ++ 0 :: 1 :: (Os ++ 1 :: (J ++ 1 :: (sv ++ 0 :: 1 :: Y2)))))
        (hdR Q.DP31 (1 :: (J ++ 1 :: (sv ++ [1]))) (1 :: Y2))) ∧
    (¬ rowsOK m (rowsOf m w m) n (w.drop (m * m)) ((Os.reverse ++ List.replicate m 2).take m) (Os.reverse.drop m) →
      zmmLogic.Reach (hd QMM.FA w.reverse (0 :: [] ++ 1 :: List.replicate m 3 ++ 0 :: 1 :: (Os ++ 1 :: (J ++ 1 :: (sv ++ 0 :: 1 :: Y2)))))
        (hdR Q.DP30 (1 :: (J ++ 1 :: (sv ++ [1]))) (1 :: Y2))) := by
  have h1u : (1 : Nat) ∈ ALL := by simp [ALL]
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have hT : Sym4 (Os ++ 1 :: (J ++ 1 :: (sv ++ 0 :: 1 :: Y2))) := by
    simp [sym4_app_iff, sym4_cons_iff, h0, h1u, hOs.sym4, hJ.sym4, hsv.sym4, hY2]
  have hRrem := rowsOf_mem m m w hw (by omega)
  have hstor : w.reverse = (w.drop (m * m)).reverse ++ stor (rowsOf m w m) := by
    rw [stor_eq, rowsOf_flatten, ← List.reverse_append, List.take_append_drop]
  have hF0 : Bits (w.drop (m * m)).reverse := fun a ha => hw a (List.mem_of_mem_drop (List.mem_reverse.mp ha))
  have hBd : Bits (stor (rowsOf m w m)) := bits_stor _ (fun r hr => (hRrem r hr).1)
  have hD := dryRows m 0 (rowsOf m w m) [] (w.drop (m * m)).reverse 0 hRrem hF0 (by simp)
    (by rw [rowsOf_length]; omega) _ hT
  have hD' : zmmLogic.Reach (hd QMM.FA w.reverse (0 :: [] ++ 1 :: List.replicate m 3 ++ 0 :: 1 :: (Os ++ 1 :: (J ++ 1 :: (sv ++ 0 :: 1 :: Y2)))))
      (hd QMM.FA (w.drop (m * m)).reverse (0 :: stor (rowsOf m w m) ++ 1 :: List.replicate m 2 ++
        0 :: 1 :: (Os ++ 1 :: (J ++ 1 :: (sv ++ 0 :: 1 :: Y2))))) := by
    refine hD.of_eq ?_ ?_
    · rw [hstor, rowsOf_length]; simp [stor]
    · simp [rowsOf_length]
  have hAne : (w.drop (m * m)).reverse ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this; omega
  obtain ⟨b, Wr, hAr⟩ : ∃ b Wr, (w.drop (m * m)).reverse = Wr ++ [b] := by
    rcases List.eq_nil_or_concat (w.drop (m * m)).reverse with h | ⟨Wr, b, h⟩
    · exact absurd h hAne
    · exact ⟨b, Wr, by rw [h]; simp⟩
  obtain ⟨x, Wt, hWe⟩ : ∃ x Wt, Wr ++ [b] = x :: Wt := List.exists_cons_of_ne_nil (by simp)
  have hF0' : Bits (Wr ++ [b]) := by rw [← hAr]; exact hF0
  have hWr : Bits Wr := fun a ha => hF0' a (by simp [ha])
  have hbb : b ∈ bits := hF0' b (by simp)
  have hRest : Sym4 (J ++ 1 :: (sv ++ 0 :: 1 :: Y2)) := by
    simp [sym4_app_iff, sym4_cons_iff, h0, h1u, hJ.sym4, hsv.sym4, hY2]
  have fin := dryFinE Wr (stor (rowsOf m w m)) Os (J ++ 1 :: (sv ++ 0 :: 1 :: Y2)) b x Wt 1 m (Or.inr rfl) hWe hWr hbb hBd hOs hRest
  rw [hAr] at hD'
  have hC : Bits ((Os.reverse ++ List.replicate m 2).take m) := fun a ha => by
    have := List.mem_of_mem_take ha
    rcases List.mem_append.mp this with h | h
    · exact hOs.rev a h
    · rw [List.eq_of_mem_replicate h]; simp [bits]
  have hClen : ((Os.reverse ++ List.replicate m 2).take m).length = m := by
    simp only [List.length_take, List.length_append, List.length_reverse, List.length_replicate]; omega
  have hOrest : Bits (Os.reverse.drop m) := fun a ha => hOs.rev a (List.mem_of_mem_drop ha)
  have hCb : ∀ a ∈ List.replicate (min m Os.length) 0, a = 0 := fun a ha => List.eq_of_mem_replicate ha
  have hB : stor (rowsOf m w m) ≠ [] := by
    intro h
    have : (stor (rowsOf m w m)).length = m * m := by
      rw [stor_eq, List.length_reverse, rowsOf_flatten]; simp only [List.length_take]; omega
    rw [h] at this
    have hmm : 0 < m * m := Nat.mul_pos hmpos hmpos
    simp only [List.length_nil] at this
    omega
  have hra := rowsAll m (rowsOf m w m) hRrem (rowsOf_length m m w) hm hB J sv Y2 hJ hsv hY2 n
    (w.drop (m * m)) ((Os.reverse ++ List.replicate m 2).take m) (Os.reverse.drop m)
    (List.replicate (min m Os.length) 0) 0
    (fun a ha => mem_bits (hw a (List.mem_of_mem_drop ha)))
    (by intro h; exact hAne (by rw [h]; rfl)) hnA hC hClen hOrest hCb
  have hconv : ∀ q, zmmLogic.Reach
      (hdR QMM.RS1 ((w.drop (m * m)).reverse ++ List.replicate 0 1 ++ 1 :: stor (rowsOf m w m) ++ 0 :: [] ++ [1])
        (0 :: ((Os.reverse ++ List.replicate m 2).take m).reverse ++ 1 :: ((Os.reverse.drop m).reverse ++
          List.replicate (min m Os.length) 0 ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2))) q →
      zmmLogic.Reach (hdR QMM.RS1 (Wr ++ [b] ++ 1 :: stor (rowsOf m w m) ++ [0, 1])
        (0 :: ((Os.reverse ++ List.replicate m 2).take m).reverse ++ [] ++
          1 :: (Os.take (Os.length - m) ++ List.replicate (min m Os.length) 0 ++ 1 :: (J ++ 1 :: (sv ++ 0 :: 1 :: Y2))))) q := by
    intro q h
    refine h.of_eq ?_ rfl
    rw [hAr, drop_rev_eq]
    simp
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact hD'.trans (fin.trans (hconv _ (hra.1 h)))
  · exact hD'.trans (fin.trans (hconv _ (hra.2 h)))

end ZP.Mul.MM
