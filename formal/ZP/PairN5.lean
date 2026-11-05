module

public import ZP.PairN4

@[expose] public section

/-! # The pair lemma of the NTT machine, part 5: the evaluation phase, pass start -/

namespace ZP.N

open ZP ZP.G


theorem psMid0 (A Xa Eb Zb Y : List Nat) (a : Nat) (f o c1 c2 : Nat) (hA : ∀ x ∈ A, x ∈ U4) (hXa : ∀ x ∈ Xa, x ∈ bits) (hEb : ∀ x ∈ Eb, x ∈ bits) (hZb : ∀ x ∈ Zb, x ∈ bits) (hY : ∀ x ∈ Y, x ∈ bits) (rest : List Nat) (hrest : NoB rest) (hf : f = 2 ∨ f = 3) (ho : o = 2 ∨ o = 3) (hc1 : c1 = 2 ∨ c1 = 3) (hc2 : c2 = 2 ∨ c2 = 3) :
    znttLogic.Reach
      (hdR QN.RH0 (A ++ [1, 1])
        ([f, o, 2, 1, c1, c2] ++ Xa ++ [1] ++ Eb ++ [1] ++ Zb ++ [1] ++ (List.replicate a 2) ++ [3] ++ Y ++ [1, 1] ++ rest))
      (hdR QN.RH0 (A ++ [1, 1, 2, o, 2, 1, 3, 2] ++ List.replicate (Xa.length) 2 ++ [1] ++ Eb ++ [1] ++ Zb ++ [1] ++ List.replicate (a) 3 ++ [3] ++ Y ++ [1, 1])
        (rest)) := by
  have hV : Valid [U4, bits, bits, bits, Mk, bits, NB] [A, Xa, Eb, Zb, List.replicate a 2, Y, rest] :=
    Valid.cons hA (Valid.cons hXa (Valid.cons hEb (Valid.cons hZb (Valid.cons (rep2_mk a) (Valid.cons hY (Valid.cons hrest (Valid.nil _)))))))
  rcases hf with rfl | rfl <;> rcases ho with rfl | rfl <;> rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 2, .sym 2, .sym 1, .sym 2, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 2, .sym 2, .sym 1, .sym 2, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 2, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 2, .sym 2, .sym 1, .sym 3, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 3, .sym 2, .sym 1, .sym 2, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 3, .sym 2, .sym 1, .sym 2, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 3, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 3, .sym 2, .sym 1, .sym 3, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 2, .sym 2, .sym 1, .sym 2, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 2, .sym 2, .sym 1, .sym 2, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 2, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 2, .sym 2, .sym 1, .sym 3, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 3, .sym 2, .sym 1, .sym 2, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 3, .sym 2, .sym 1, .sym 2, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 3, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 3, .sym 2, .sym 1, .sym 3, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem psMid1 (A Xa Eb Zb Y : List Nat) (a : Nat) (f o c1 c2 : Nat) (hA : ∀ x ∈ A, x ∈ U4) (hXa : ∀ x ∈ Xa, x ∈ bits) (hEb : ∀ x ∈ Eb, x ∈ bits) (hZb : ∀ x ∈ Zb, x ∈ bits) (hY : ∀ x ∈ Y, x ∈ bits) (rest : List Nat) (hrest : NoB rest) (hf : f = 2 ∨ f = 3) (ho : o = 2 ∨ o = 3) (hc1 : c1 = 2 ∨ c1 = 3) (hc2 : c2 = 2 ∨ c2 = 3) :
    znttLogic.Reach
      (hdR QN.RH0 (A ++ [1, 1])
        ([f, o, 3, 1, c1, c2] ++ Xa ++ [1] ++ Eb ++ [1] ++ Zb ++ [1] ++ (List.replicate a 2) ++ [3] ++ Y ++ [1, 1] ++ rest))
      (hdR QN.RH0 (A ++ [1, 1, 2, o, 3, 1, 3, 3] ++ List.replicate (Xa.length) 2 ++ [1] ++ Eb ++ [1] ++ Zb ++ [1] ++ List.replicate (a) 3 ++ [3] ++ Y ++ [1, 1])
        (rest)) := by
  have hV : Valid [U4, bits, bits, bits, Mk, bits, NB] [A, Xa, Eb, Zb, List.replicate a 2, Y, rest] :=
    Valid.cons hA (Valid.cons hXa (Valid.cons hEb (Valid.cons hZb (Valid.cons (rep2_mk a) (Valid.cons hY (Valid.cons hrest (Valid.nil _)))))))
  rcases hf with rfl | rfl <;> rcases ho with rfl | rfl <;> rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 2, .sym 3, .sym 1, .sym 2, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 2, .sym 3, .sym 1, .sym 2, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 2, .sym 3, .sym 1, .sym 3, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 2, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 3, .sym 3, .sym 1, .sym 2, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 3, .sym 3, .sym 1, .sym 2, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 3, .sym 3, .sym 1, .sym 3, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 3, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 2, .sym 3, .sym 1, .sym 2, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 2, .sym 3, .sym 1, .sym 2, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 2, .sym 3, .sym 1, .sym 3, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 2, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 3, .sym 3, .sym 1, .sym 2, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 3, .sym 3, .sym 1, .sym 2, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 3, .sym 3, .sym 1, .sym 3, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y, rest]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 3, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id, .sym 1, .sym 1]) (rs' := [.blk 6 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem psLast0 (A Xa Eb Zb Y : List Nat) (a : Nat) (f o c1 c2 : Nat) (hA : ∀ x ∈ A, x ∈ U4) (hXa : ∀ x ∈ Xa, x ∈ bits) (hEb : ∀ x ∈ Eb, x ∈ bits) (hZb : ∀ x ∈ Zb, x ∈ bits) (hY : ∀ x ∈ Y, x ∈ bits) (hf : f = 2 ∨ f = 3) (ho : o = 2 ∨ o = 3) (hc1 : c1 = 2 ∨ c1 = 3) (hc2 : c2 = 2 ∨ c2 = 3) :
    znttLogic.Reach
      (hdR QN.RH0 (A ++ [1, 1])
        ([f, o, 2, 1, c1, c2] ++ Xa ++ [1] ++ Eb ++ [1] ++ Zb ++ [1] ++ (List.replicate a 2) ++ [3] ++ Y))
      (hdR QN.RU2 (A ++ [1, 1, 2, o, 2, 1, 3, 2] ++ List.replicate (Xa.length) 2 ++ [1] ++ Eb ++ [1] ++ Zb ++ [1] ++ List.replicate (a) 3 ++ [3] ++ Y)
        ([])) := by
  have hV : Valid [U4, bits, bits, bits, Mk, bits] [A, Xa, Eb, Zb, List.replicate a 2, Y] :=
    Valid.cons hA (Valid.cons hXa (Valid.cons hEb (Valid.cons hZb (Valid.cons (rep2_mk a) (Valid.cons hY (Valid.nil _))))))
  rcases hf with rfl | rfl <;> rcases ho with rfl | rfl <;> rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 2, .sym 2, .sym 1, .sym 2, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 2, .sym 2, .sym 1, .sym 2, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 2, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 2, .sym 2, .sym 1, .sym 3, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 3, .sym 2, .sym 1, .sym 2, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 3, .sym 2, .sym 1, .sym 2, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 3, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 3, .sym 2, .sym 1, .sym 3, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 2, .sym 2, .sym 1, .sym 2, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 2, .sym 2, .sym 1, .sym 2, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 2, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 2, .sym 2, .sym 1, .sym 3, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 3, .sym 2, .sym 1, .sym 2, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 3, .sym 2, .sym 1, .sym 2, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 3, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 3, .sym 2, .sym 1, .sym 3, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 2, .sym 1, .sym 3, .sym 2, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem psLast1 (A Xa Eb Zb Y : List Nat) (a : Nat) (f o c1 c2 : Nat) (hA : ∀ x ∈ A, x ∈ U4) (hXa : ∀ x ∈ Xa, x ∈ bits) (hEb : ∀ x ∈ Eb, x ∈ bits) (hZb : ∀ x ∈ Zb, x ∈ bits) (hY : ∀ x ∈ Y, x ∈ bits) (hf : f = 2 ∨ f = 3) (ho : o = 2 ∨ o = 3) (hc1 : c1 = 2 ∨ c1 = 3) (hc2 : c2 = 2 ∨ c2 = 3) :
    znttLogic.Reach
      (hdR QN.RH0 (A ++ [1, 1])
        ([f, o, 3, 1, c1, c2] ++ Xa ++ [1] ++ Eb ++ [1] ++ Zb ++ [1] ++ (List.replicate a 2) ++ [3] ++ Y))
      (hdR QN.RU2 (A ++ [1, 1, 2, o, 3, 1, 3, 3] ++ List.replicate (Xa.length) 2 ++ [1] ++ Eb ++ [1] ++ Zb ++ [1] ++ List.replicate (a) 3 ++ [3] ++ Y)
        ([])) := by
  have hV : Valid [U4, bits, bits, bits, Mk, bits] [A, Xa, Eb, Zb, List.replicate a 2, Y] :=
    Valid.cons hA (Valid.cons hXa (Valid.cons hEb (Valid.cons hZb (Valid.cons (rep2_mk a) (Valid.cons hY (Valid.nil _))))))
  rcases hf with rfl | rfl <;> rcases ho with rfl | rfl <;> rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 2, .sym 3, .sym 1, .sym 2, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 2, .sym 3, .sym 1, .sym 2, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 2, .sym 3, .sym 1, .sym 3, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 2, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 3, .sym 3, .sym 1, .sym 2, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 3, .sym 3, .sym 1, .sym 2, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 3, .sym 3, .sym 1, .sym 3, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 2, .sym 3, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 2, .sym 3, .sym 1, .sym 2, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 2, .sym 3, .sym 1, .sym 2, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 2, .sym 3, .sym 1, .sym 3, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 2, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 3, .sym 3, .sym 1, .sym 2, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 3, .sym 3, .sym 1, .sym 2, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 3, .sym 3, .sym 1, .sym 3, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [A, Xa, Eb, Zb, List.replicate a 2, Y]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1]) (rs := [.sym 3, .sym 3, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 3, .sym 1, .sym 3, .sym 3, .blk 1 (.const 2), .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 (.const 3), .sym 3, .blk 5 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-! ## Evaluation-phase records -/

/-- A record of the evaluation phase: header cells `F O P` and the cells of the four fields
(after their `M`). -/
structure ER where
  f : Nat
  o : Nat
  pf : Nat
  acc : List Nat
  E : List Nat
  z : List Nat
  u : List Nat

/-- The part of a record after its `MM`. -/
def ER.tl (r : ER) : List Nat :=
  [r.f, r.o, r.pf, 1] ++ r.acc ++ [1] ++ r.E ++ [1] ++ r.z ++ [1] ++ r.u

def eTape : List ER → List Nat
  | [] => []
  | r :: rs => [1, 1] ++ r.tl ++ eTape rs

def Bits (l : List Nat) : Prop := ∀ x ∈ l, x ∈ bits

theorem Bits.app {u v : List Nat} (hu : Bits u) (hv : Bits v) : Bits (u ++ v) := fun x hx => by
  rcases List.mem_append.1 hx with h | h
  · exact hu x h
  · exact hv x h

theorem Bits.cons {a : Nat} {l : List Nat} (ha : a ∈ bits) (h : Bits l) : Bits (a :: l) := fun x hx => by
  rcases List.mem_cons.1 hx with rfl | hx
  · exact ha
  · exact h x hx

theorem Bits.nil : Bits [] := fun x hx => by simp at hx

theorem Bits.rep (k a : Nat) (ha : a ∈ bits) : Bits (List.replicate k a) := fun x hx => by
  rw [List.eq_of_mem_replicate hx]; exact ha

/-- A well-formed record: header cells are bits, the fields are bit strings. -/
structure ER.ok (r : ER) : Prop where
  f : r.f = 2 ∨ r.f = 3
  o : r.o = 2 ∨ r.o = 3
  pf : r.pf = 2 ∨ r.pf = 3
  acc : Bits r.acc
  E : Bits r.E
  z : Bits r.z
  u : Bits r.u

theorem bits_mem {a : Nat} (h : a = 2 ∨ a = 3) : a ∈ bits := by
  rcases h with rfl | rfl <;> simp [bits]

theorem bits_nb {y : Nat} (h : y ∈ bits) : y ∈ NB := by
  simp only [bits, NB, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega

theorem nb_u4 {y : Nat} (h : y ∈ NB) : y ∈ U4 := by
  simp only [NB, U4, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega

theorem ER.tl_nb (r : ER) (h : r.ok) : NoB r.tl := by
  unfold ER.tl
  have hbn : ∀ l, Bits l → NoB l := fun l hl x hx => bits_nb (hl x hx)
  have h1 : NoB [r.f, r.o, r.pf, 1] := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact bits_nb (bits_mem h.f)
    · exact bits_nb (bits_mem h.o)
    · exact bits_nb (bits_mem h.pf)
    · simp [NB]
  have hone : NoB [1] := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; simp [NB]
  exact noB_app (noB_app (noB_app (noB_app (noB_app (noB_app (noB_app h1 (hbn _ h.acc)) hone) (hbn _ h.E)) hone)
    (hbn _ h.z)) hone) (hbn _ h.u)

theorem noB_eTape : ∀ L : List ER, (∀ r ∈ L, r.ok) → NoB (eTape L)
  | [], _ => noB_nil
  | r :: L, h => by
    intro x hx
    simp only [eTape, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (hx | hx) | hx
    · rcases hx with rfl | rfl <;> simp [NB]
    · exact r.tl_nb (h r (by simp)) x hx
    · exact noB_eTape L (fun r' hr' => h r' (by simp [hr'])) x hx

theorem u4_of_nb {l : List Nat} (h : NoB l) : ∀ x ∈ l, x ∈ U4 := fun x hx => nb_u4 (h x hx)

/-! ## Pass start -/

/-- Restore a pointer: the leading marks become ones again. -/
def restoreU : List Nat → List Nat
  | 2 :: l => 3 :: restoreU l
  | l => l

theorem restoreU_rep (a : Nat) (Y : List Nat) : restoreU (List.replicate a 2 ++ 3 :: Y) = List.replicate a 3 ++ 3 :: Y := by
  induction a with
  | zero => rfl
  | succ a ih => simp [List.replicate_succ, restoreU, ih]

/-- The accumulator at the start of a pass: `x_j` (a `1` iff the input flag is set). -/
def accInit (x : Bool) (n : Nat) : List Nat :=
  3 :: (if x then 3 :: List.replicate (n - 2) 2 else List.replicate (n - 1) 2)

def ER.ps (r : ER) : ER :=
  { r with f := 2, acc := accInit (r.pf == 3) r.acc.length, u := restoreU r.u }

/-- The shape needed at the start of a pass. -/
structure ER.psOk (r : ER) : Prop where
  ok : r.ok
  accShape : ∃ c1 c2 X, r.acc = c1 :: c2 :: X
  uShape : ∃ a Y, r.u = List.replicate a 2 ++ 3 :: Y

theorem restoreU_bits (l : List Nat) (h : Bits l) : Bits (restoreU l) := by
  induction l with
  | nil => exact h
  | cons x l ih =>
    have hx : x ∈ bits := h x (by simp)
    have hl : Bits l := fun y hy => h y (by simp [hy])
    by_cases h2 : x = 2
    · subst h2
      simp only [restoreU]
      exact Bits.cons (by simp [bits]) (ih hl)
    · have : restoreU (x :: l) = x :: l := by
        cases x with
        | zero => rfl
        | succ x =>
          cases x with
          | zero => rfl
          | succ x => cases x with
            | zero => exact absurd rfl h2
            | succ x => rfl
      rw [this]; exact h

theorem accInit_bits (x : Bool) (n : Nat) : Bits (accInit x n) := by
  unfold accInit
  apply Bits.cons (by simp [bits])
  split
  · exact Bits.cons (by simp [bits]) (Bits.rep _ _ (by simp [bits]))
  · exact Bits.rep _ _ (by simp [bits])

theorem ER.ps_ok (r : ER) (h : r.ok) : r.ps.ok where
  f := Or.inl rfl
  o := h.o
  pf := h.pf
  acc := accInit_bits _ _
  E := h.E
  z := h.z
  u := restoreU_bits _ h.u

theorem psMidER (A : List Nat) (hA : ∀ x ∈ A, x ∈ U4) (r : ER) (h : r.psOk) (rest : List Nat) (hrest : NoB rest) :
    znttLogic.Reach
      (hdR QN.RH0 (A ++ [1, 1]) (r.tl ++ [1, 1] ++ rest))
      (hdR QN.RH0 (A ++ [1, 1] ++ r.ps.tl ++ [1, 1]) rest) := by
  obtain ⟨⟨hf, ho, hpf, hacc, hE, hz, hu⟩, ⟨c1, c2, X, hX⟩, ⟨a, Y, hY⟩⟩ := h
  have hX' : Bits X := fun x hx => hacc x (by rw [hX]; simp [hx])
  have hc1 : c1 = 2 ∨ c1 = 3 := by
    have := hacc c1 (by rw [hX]; simp); simp [bits] at this; omega
  have hc2 : c2 = 2 ∨ c2 = 3 := by
    have := hacc c2 (by rw [hX]; simp); simp [bits] at this; omega
  have hY' : Bits Y := fun x hx => hu x (by rw [hY]; simp [hx])
  rcases hpf with hp | hp
  · have := psMid0 A X r.E r.z Y a r.f r.o c1 c2 hA hX' hE hz hY' rest hrest hf ho hc1 hc2
    refine this.of_eq ?_ ?_
    · simp [ER.tl, hX, hY, hp, List.append_assoc]
    · simp [ER.tl, ER.ps, hX, hY, hp, accInit, restoreU_rep, List.replicate_succ, List.append_assoc]
  · have := psMid1 A X r.E r.z Y a r.f r.o c1 c2 hA hX' hE hz hY' rest hrest hf ho hc1 hc2
    refine this.of_eq ?_ ?_
    · simp [ER.tl, hX, hY, hp, List.append_assoc]
    · simp [ER.tl, ER.ps, hX, hY, hp, accInit, restoreU_rep, List.replicate_succ, List.append_assoc]

theorem psLastER (A : List Nat) (hA : ∀ x ∈ A, x ∈ U4) (r : ER) (h : r.psOk) :
    znttLogic.Reach
      (hdR QN.RH0 (A ++ [1, 1]) r.tl)
      (hdR QN.RU2 (A ++ [1, 1] ++ r.ps.tl) []) := by
  obtain ⟨⟨hf, ho, hpf, hacc, hE, hz, hu⟩, ⟨c1, c2, X, hX⟩, ⟨a, Y, hY⟩⟩ := h
  have hX' : Bits X := fun x hx => hacc x (by rw [hX]; simp [hx])
  have hc1 : c1 = 2 ∨ c1 = 3 := by
    have := hacc c1 (by rw [hX]; simp); simp [bits] at this; omega
  have hc2 : c2 = 2 ∨ c2 = 3 := by
    have := hacc c2 (by rw [hX]; simp); simp [bits] at this; omega
  have hY' : Bits Y := fun x hx => hu x (by rw [hY]; simp [hx])
  rcases hpf with hp | hp
  · have := psLast0 A X r.E r.z Y a r.f r.o c1 c2 hA hX' hE hz hY' hf ho hc1 hc2
    refine this.of_eq ?_ ?_
    · simp [ER.tl, hX, hY, hp, List.append_assoc]
    · simp [ER.tl, ER.ps, hX, hY, hp, accInit, restoreU_rep, List.replicate_succ, List.append_assoc]
  · have := psLast1 A X r.E r.z Y a r.f r.o c1 c2 hA hX' hE hz hY' hf ho hc1 hc2
    refine this.of_eq ?_ ?_
    · simp [ER.tl, hX, hY, hp, List.append_assoc]
    · simp [ER.tl, ER.ps, hX, hY, hp, accInit, restoreU_rep, List.replicate_succ, List.append_assoc]

theorem psLoop : ∀ (L : List ER) (r : ER), r.psOk → (∀ r' ∈ L, r'.psOk) → ∀ (A : List Nat), (∀ x ∈ A, x ∈ U4) →
    znttLogic.Reach
      (hdR QN.RH0 (A ++ [1, 1]) (r.tl ++ eTape L))
      (hdR QN.RU2 (A ++ eTape ((r :: L).map ER.ps)) [])
  | [], r, hr, _, A, hA => by
    have := psLastER A hA r hr
    refine this.of_eq ?_ ?_
    · simp [eTape]
    · simp [eTape, List.append_assoc]
  | r' :: L, r, hr, hL, A, hA => by
    have hr' : r'.psOk := hL r' (by simp)
    have hLok : ∀ x ∈ L, x.ok := fun x hx => (hL x (by simp [hx])).ok
    have h1 := psMidER A hA r hr (r'.tl ++ eTape L)
      (noB_app (r'.tl_nb hr'.ok) (noB_eTape L hLok))
    have h2 := psLoop L r' hr' (fun x hx => hL x (by simp [hx])) (A ++ [1, 1] ++ r.ps.tl) (by
      intro x hx
      simp only [List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact hA x hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> simp [U4]
      · exact u4_of_nb (r.ps.tl_nb (r.ps_ok hr.ok)) x hx)
    have h1' : znttLogic.Reach
        (hdR QN.RH0 (A ++ [1, 1]) (r.tl ++ eTape (r' :: L)))
        (hdR QN.RH0 (A ++ [1, 1] ++ r.ps.tl ++ [1, 1]) (r'.tl ++ eTape L)) := by
      refine h1.of_eq ?_ ?_
      · simp [eTape, List.append_assoc]
      · rfl
    refine h1'.trans (h2.of_eq rfl ?_)
    simp [eTape, List.append_assoc]

theorem psStart (a c n : Nat) (Pb Tl : List Nat) (pc : Nat) (hPb : ∀ x ∈ Pb, x ∈ bits) (hTl : NoB Tl) (hpc : pc = 2 ∨ pc = 3) :
    znttLogic.Reach
      (hd QN.RZ0 ([0, 3, 3] ++ (List.replicate a 3) ++ [1, pc] ++ Pb ++ [1, 3, 3, 3, 1, 3] ++ (List.replicate c 3) ++ [1, 3] ++ (List.replicate n 3) ++ [1, 1] ++ Tl)
        ([0]))
      (hdR QN.RH0 ([0, 3, 3] ++ (List.replicate a 3) ++ [1, pc] ++ Pb ++ [1, 3, 3, 3, 1, 3] ++ (List.replicate c 3) ++ [1, 3] ++ (List.replicate n 3) ++ [1, 1])
        (Tl)) := by
  have hV : Valid [T3, bits, T3, T3, NB] [List.replicate a 3, Pb, List.replicate c 3, List.replicate n 3, Tl] :=
    Valid.cons (rep_t3 a) (Valid.cons hPb (Valid.cons (rep_t3 c) (Valid.cons (rep_t3 n) (Valid.cons hTl (Valid.nil _)))))
  rcases hpc with rfl | rfl
  · exact checkTF (env := [List.replicate a 3, Pb, List.replicate c 3, List.replicate n 3, Tl]) (E := []) (k := 120) hV trivial
      (ls := [.sym 0, .sym 3, .sym 3, .blk 0 .id, .sym 1, .sym 2, .blk 1 .id, .sym 1, .sym 3, .sym 3, .sym 3, .sym 1, .sym 3, .blk 2 .id, .sym 1, .sym 3, .blk 3 .id, .sym 1, .sym 1, .blk 4 .id]) (rs := [.sym 0])
      (ls' := [.sym 0, .sym 3, .sym 3, .blk 0 .id, .sym 1, .sym 2, .blk 1 .id, .sym 1, .sym 3, .sym 3, .sym 3, .sym 1, .sym 3, .blk 2 .id, .sym 1, .sym 3, .blk 3 .id, .sym 1, .sym 1]) (rs' := [.blk 4 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkTF (env := [List.replicate a 3, Pb, List.replicate c 3, List.replicate n 3, Tl]) (E := []) (k := 120) hV trivial
      (ls := [.sym 0, .sym 3, .sym 3, .blk 0 .id, .sym 1, .sym 3, .blk 1 .id, .sym 1, .sym 3, .sym 3, .sym 3, .sym 1, .sym 3, .blk 2 .id, .sym 1, .sym 3, .blk 3 .id, .sym 1, .sym 1, .blk 4 .id]) (rs := [.sym 0])
      (ls' := [.sym 0, .sym 3, .sym 3, .blk 0 .id, .sym 1, .sym 3, .blk 1 .id, .sym 1, .sym 3, .sym 3, .sym 3, .sym 1, .sym 3, .blk 2 .id, .sym 1, .sym 3, .blk 3 .id, .sym 1, .sym 1]) (rs' := [.blk 4 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem psEnd (a c n : Nat) (Pb Tl : List Nat) (pc : Nat) (hPb : ∀ x ∈ Pb, x ∈ bits) (hTl : NoB Tl) (hpc : pc = 2 ∨ pc = 3) :
    znttLogic.Reach
      (hdR QN.RU2 ([0, 3, 3] ++ (List.replicate a 3) ++ [1, pc] ++ Pb ++ [1, 3, 3, 3, 1, 3] ++ (List.replicate c 3) ++ [1, 3] ++ (List.replicate n 3) ++ [1, 1] ++ Tl)
        ([]))
      (hdR QN.FA0 ([0, 3, 3] ++ (List.replicate a 3) ++ [1, pc] ++ Pb ++ [1, 3, 3, 3, 1, 3] ++ (List.replicate c 3) ++ [1, 3] ++ (List.replicate n 3) ++ [1, 1])
        (Tl)) := by
  have hV : Valid [T3, bits, T3, T3, NB] [List.replicate a 3, Pb, List.replicate c 3, List.replicate n 3, Tl] :=
    Valid.cons (rep_t3 a) (Valid.cons hPb (Valid.cons (rep_t3 c) (Valid.cons (rep_t3 n) (Valid.cons hTl (Valid.nil _)))))
  rcases hpc with rfl | rfl
  · exact checkFF (env := [List.replicate a 3, Pb, List.replicate c 3, List.replicate n 3, Tl]) (E := []) (k := 120) hV trivial
      (ls := [.sym 0, .sym 3, .sym 3, .blk 0 .id, .sym 1, .sym 2, .blk 1 .id, .sym 1, .sym 3, .sym 3, .sym 3, .sym 1, .sym 3, .blk 2 .id, .sym 1, .sym 3, .blk 3 .id, .sym 1, .sym 1, .blk 4 .id]) (rs := [])
      (ls' := [.sym 0, .sym 3, .sym 3, .blk 0 .id, .sym 1, .sym 2, .blk 1 .id, .sym 1, .sym 3, .sym 3, .sym 3, .sym 1, .sym 3, .blk 2 .id, .sym 1, .sym 3, .blk 3 .id, .sym 1, .sym 1]) (rs' := [.blk 4 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [List.replicate a 3, Pb, List.replicate c 3, List.replicate n 3, Tl]) (E := []) (k := 120) hV trivial
      (ls := [.sym 0, .sym 3, .sym 3, .blk 0 .id, .sym 1, .sym 3, .blk 1 .id, .sym 1, .sym 3, .sym 3, .sym 3, .sym 1, .sym 3, .blk 2 .id, .sym 1, .sym 3, .blk 3 .id, .sym 1, .sym 1, .blk 4 .id]) (rs := [])
      (ls' := [.sym 0, .sym 3, .sym 3, .blk 0 .id, .sym 1, .sym 3, .blk 1 .id, .sym 1, .sym 3, .sym 3, .sym 3, .sym 1, .sym 3, .blk 2 .id, .sym 1, .sym 3, .blk 3 .id, .sym 1, .sym 1]) (rs' := [.blk 4 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- The parameter area during the evaluation: `W M P M K M C M Nn`, `P` carrying the register `S`. -/
def EPre (a c n pc : Nat) (Pb : List Nat) : List Nat :=
  [0, 3, 3] ++ List.replicate a 3 ++ [1, pc] ++ Pb ++ [1, 3, 3, 3, 1, 3] ++ List.replicate c 3 ++ [1, 3] ++ List.replicate n 3

theorem EPre_u4 (a c n pc : Nat) (Pb : List Nat) (hpc : pc = 2 ∨ pc = 3) (hPb : Bits Pb) : ∀ x ∈ EPre a c n pc Pb, x ∈ U4 := by
  intro x hx
  by_cases hP : x ∈ Pb
  · have := hPb x hP
    simp only [bits, U4, List.mem_cons, List.not_mem_nil, or_false] at this ⊢
    omega
  · simp only [EPre, List.mem_append, List.mem_cons, List.mem_replicate, List.not_mem_nil, or_false, hP] at hx
    simp only [U4, List.mem_cons, List.not_mem_nil, or_false]
    omega

/-- A pass start: `F := 0`, `acc := x_j`, pointers restored; the head returns to the first record. -/
theorem passStart (a c n pc : Nat) (Pb : List Nat) (hpc : pc = 2 ∨ pc = 3) (hPb : Bits Pb)
    (r : ER) (L : List ER) (hr : r.psOk) (hL : ∀ r' ∈ L, r'.psOk) :
    znttLogic.Reach
      (hd QN.RZ0 (EPre a c n pc Pb ++ eTape (r :: L)) [0])
      (hdR QN.FA0 (EPre a c n pc Pb ++ [1, 1]) (r.ps.tl ++ eTape (L.map ER.ps))) := by
  have hLok : ∀ x ∈ L, x.ok := fun x hx => (hL x hx).ok
  have h1 := psStart a c n Pb (r.tl ++ eTape L) pc hPb (noB_app (r.tl_nb hr.ok) (noB_eTape L hLok)) hpc
  have h2 := psLoop L r hr hL (EPre a c n pc Pb) (EPre_u4 a c n pc Pb hpc hPb)
  have hok : ∀ x ∈ (r :: L).map ER.ps, x.ok := by
    intro x hx
    simp only [List.mem_map, List.mem_cons] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rcases hy with rfl | hy
    · exact y.ps_ok hr.ok
    · exact y.ps_ok (hL y hy).ok
  have h3 := psEnd a c n Pb (r.ps.tl ++ eTape (L.map ER.ps)) pc hPb (noB_app (r.ps.tl_nb (r.ps_ok hr.ok)) (noB_eTape _ (by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact y.ps_ok (hL y hy).ok))) hpc
  have h1' : znttLogic.Reach
      (hd QN.RZ0 (EPre a c n pc Pb ++ eTape (r :: L)) [0])
      (hdR QN.RH0 (EPre a c n pc Pb ++ [1, 1]) (r.tl ++ eTape L)) := by
    refine h1.of_eq ?_ ?_
    · simp [EPre, eTape, List.replicate_succ, List.append_assoc]
    · simp [EPre, List.append_assoc]
  have h3' : znttLogic.Reach
      (hdR QN.RU2 (EPre a c n pc Pb ++ eTape ((r :: L).map ER.ps)) [])
      (hdR QN.FA0 (EPre a c n pc Pb ++ [1, 1]) (r.ps.tl ++ eTape (L.map ER.ps))) := by
    refine h3.of_eq ?_ ?_
    · simp [EPre, eTape, List.append_assoc]
    · simp [EPre, List.append_assoc]
  exact h1'.trans (h2.trans h3')

end ZP.N
