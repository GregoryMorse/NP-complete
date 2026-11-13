module

public import ZP.MulGuardSeg
public import ZP.PairF

@[expose] public section

/-!
# Z_MUL: the output guard

The output must be a pair numeral `1 b₁ … 1 bₖ` (`pairVal`). The machine scans it from its last cell
(`scan`); `scan_rev` says this is `pairOk`, and `checkMul_machine` says that `checkMul` is the guard
followed by the old comparison `N[0] = N[1] N[2]` on `numbers (out 0 s)`. `guardRun` runs the guard on the
logical machine: it passes to `mK1` at the `M` after the output, or fails at `DP10`, the output erased.
-/

namespace ZP.MulGuard

open ZP

/-- The guard as the machine runs it, from the last cell of `out`: `p = true` expects a digit cell, `false`
the `1` before it. -/
def scan : Bool → List Bool → Bool
  | true, [] => true
  | false, [] => false
  | true, _ :: r => scan false r
  | false, true :: r => scan true r
  | false, false :: _ => false

def pairOk : List Bool → Bool
  | [] => true
  | true :: _ :: r => pairOk r
  | _ => false

theorem scan_snoc_t (b : Bool) : ∀ (p : Bool) (x : List Bool), scan p (x ++ [b, true]) = scan p x
  | true, [] => by cases b <;> rfl
  | false, [] => by cases b <;> rfl
  | true, _ :: r => by simp only [List.cons_append, scan]; exact scan_snoc_t b false r
  | false, true :: r => by simp only [List.cons_append, scan]; exact scan_snoc_t b true r
  | false, false :: r => by simp [scan]

theorem scan_snoc_f (b : Bool) : ∀ (p : Bool) (x : List Bool), scan p (x ++ [b, false]) = false
  | true, [] => by cases b <;> rfl
  | false, [] => by cases b <;> rfl
  | true, _ :: r => by simp only [List.cons_append, scan]; exact scan_snoc_f b false r
  | false, true :: r => by simp only [List.cons_append, scan]; exact scan_snoc_f b true r
  | false, false :: r => by simp [scan]

theorem scan_rev : ∀ l : List Bool, scan true l.reverse = pairOk l
  | [] => rfl
  | [a] => by simp [scan, pairOk]
  | true :: b :: r => by
    rw [show (true :: b :: r).reverse = r.reverse ++ [b, true] by simp, scan_snoc_t, scan_rev r]; rfl
  | false :: b :: r => by
    rw [show (false :: b :: r).reverse = r.reverse ++ [b, false] by simp, scan_snoc_f]; rfl

theorem pairVal_isSome : ∀ (acc : Nat) (l : List Bool), (pairVal acc l).isSome = pairOk l
  | _, [] => rfl
  | _, [true] => rfl
  | _, [false] => rfl
  | acc, true :: b :: r => by simp only [pairVal, pairOk]; exact pairVal_isSome _ r
  | _, false :: _ :: _ => rfl

theorem numsAux_fuel : ∀ (f g : Nat) (r : List Bool) (c : Nat), r.length ≤ f → r.length ≤ g →
    numsAux f r c = numsAux g r c
  | 0, 0, _, _, _, _ => rfl
  | 0, _ + 1, r, c, h, _ => by
    have : r = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [numsAux]
  | _ + 1, 0, r, c, _, h => by
    have : r = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [numsAux]
  | _ + 1, _ + 1, [], _, _, _ => by simp [numsAux]
  | _ + 1, _ + 1, [true], _, _, _ => by simp [numsAux]
  | f + 1, g + 1, true :: b :: r, c, hf, hg => by
    simp only [numsAux]; exact numsAux_fuel f g r _ (by simp at hf; omega) (by simp at hg; omega)
  | f + 1, g + 1, false :: r, c, hf, hg => by
    simp only [numsAux]; rw [numsAux_fuel f g r 0 (by simp at hf; omega) (by simp at hg; omega)]

theorem nums_pair : ∀ (acc : Nat) (out : List Bool) (z : Nat) (s : List Bool) (f : Nat),
    pairVal acc out = some z → out.length + 1 + s.length ≤ f →
    numsAux f (out ++ false :: s) acc = z :: numsAux s.length s 0
  | acc, [], z, s, f, h, hf => by
    simp [pairVal] at h; subst h
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    simp only [List.nil_append, numsAux]
    rw [numsAux_fuel f' s.length s 0 (by simp at hf; omega) (Nat.le_refl _)]
  | acc, true :: b :: r, z, s, f, h, hf => by
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    simp only [pairVal] at h
    simp only [List.cons_append, numsAux]
    exact nums_pair _ r z s f' h (by simp at hf; omega)
  | _, [true], _, _, _, h, _ => by simp [pairVal] at h
  | _, [false], _, _, _, h, _ => by simp [pairVal] at h
  | _, false :: _ :: _, _, _, _, h, _ => by simp [pairVal] at h

/-- The machine's form of the check: the guard, then `N[0] = N[1] N[2]` for `N = numbers (out 0 s)`. -/
theorem checkMul_machine (out s : List Bool) :
    checkMul out s = (pairOk out && (let N := numbers (out ++ false :: s) ++ [0, 0]
      N.getD 0 0 == N.getD 1 0 * N.getD 2 0)) := by
  unfold checkMul
  cases hv : pairVal 0 out with
  | none =>
    have := pairVal_isSome 0 out; rw [hv] at this; simp [← this]
  | some z =>
    have hp : pairOk out = true := by have := pairVal_isSome 0 out; rw [hv] at this; simpa using this.symm
    have hn : numbers (out ++ false :: s) = z :: numbers s := by
      unfold numbers; exact nums_pair 0 out z s _ hv (by simp; omega)
    rw [hp, hn]
    simp only [Bool.true_and, List.cons_append]
    rcases hs : numbers s ++ [0, 0] with _ | ⟨x, _ | ⟨y, rest⟩⟩ <;> simp_all [List.getD]

end ZP.MulGuard

namespace ZP.Mul

open ZP

theorem hdR_rep0 (q n : Nat) (A R : List Nat) : hdR q (List.replicate n 0 ++ A) R = hdR q A R :=
  ZP.F.hdR_zeros q (List.replicate n 0) A R (fun a ha => by
    have := List.eq_of_mem_replicate ha
    subst this
    simp [ZP.F.B0])

theorem hdR_z0 (q : Nat) (Z A R : List Nat) (hZ : ∀ a ∈ Z, a = 0) : hdR q (Z ++ A) R = hdR q A R :=
  ZP.F.hdR_zeros q Z A R (fun a ha => by rw [hZ a ha]; simp [ZP.F.B0])

theorem s24 (P : List Nat) (hP : Bits P) : Sym4 ([2] ++ P) := Sym4.cons (by simp [ALL]) hP.sym4

theorem s14 (W : List Nat) (hW : Sym4 W) : Sym4 ([1] ++ W) := Sym4.cons (by simp [ALL]) hW

theorem sw (r : List Bool) (W : List Nat) (hW : Sym4 W) : Sym4 (bitsOf r ++ [1] ++ W) := by
  rw [List.append_assoc]; exact (Bits.ofB r).sym4.app (s14 W hW)

theorem bit_mem (b : Bool) : (if b then 3 else 2) ∈ bits := by cases b <;> simp [bits]

/-- The guard on the logical machine, from `mK1` (`p`) or `mKP` (`¬ p`) with the scanned cells `P` on the
left. -/
theorem guardRun (W : List Nat) (hW : Sym4 W) :
    ∀ (l : List Bool) (p : Bool) (P : List Nat), Bits P →
      zmulLogic.Reach (hdR (if p then QMul.mK1 else QMul.mKP) ([2] ++ P) (bitsOf l ++ [1] ++ W))
        (if MulGuard.scan p l then hdR QMul.mK1 ([2] ++ P ++ bitsOf l) ([1] ++ W) else hdR Q.DP10 [1] W)
  | [], true, P, _ => by
    simp only [MulGuard.scan, ite_true]
    exact (LTM.Reach.refl _ _).of_eq rfl (by simp [bitsOf])
  | [], false, P, hP => by
    simp only [MulGuard.scan, Bool.false_eq_true, ite_false]
    have h := gFailM P W hP hW
    rw [show ([0, 2] ++ P) = List.replicate 1 0 ++ ([2] ++ P) by rfl, hdR_rep0,
      hdR_z0 Q.DP10 ([0, 0] ++ List.replicate P.length 0) [1] W (by simp)] at h
    exact h.of_eq (by simp [bitsOf]) rfl
  | b :: r, true, P, hP => by
    have h1 := gDig ([2] ++ P) (bitsOf r ++ [1] ++ W) (if b then 3 else 2)
      (s24 P hP) (sw r W hW) (bit_mem b)
    have h2 := guardRun W hW r false (P ++ [if b then 3 else 2]) (hP.snoc (bit_mem b))
    simp only [MulGuard.scan, ite_true]
    simp only [Bool.false_eq_true, ite_false] at h2
    refine (h1.of_eq (by simp [bitsOf]) (by simp)).trans (h2.of_eq rfl ?_)
    simp [bitsOf]
  | true :: r, false, P, hP => by
    have h1 := gOne ([2] ++ P) (bitsOf r ++ [1] ++ W)
      (s24 P hP) (sw r W hW)
    have h2 := guardRun W hW r true (P ++ [3]) (hP.snoc (by simp [bits]))
    simp only [MulGuard.scan, Bool.false_eq_true, ite_false]
    simp only [ite_true] at h2
    refine (h1.of_eq (by simp [bitsOf]) (by simp)).trans (h2.of_eq rfl ?_)
    simp [bitsOf]
  | false :: r, false, P, hP => by
    simp only [MulGuard.scan, Bool.false_eq_true, ite_false]
    have h := gFail0 P (bitsOf r) W hP (Bits.ofB r) hW
    rw [show ([0, 2] ++ P) = List.replicate 1 0 ++ ([2] ++ P) by rfl, hdR_rep0,
      hdR_z0 Q.DP10 ([0, 0] ++ List.replicate P.length 0 ++ [0] ++ List.replicate (bitsOf r).length 0) [1] W
        (by simp; omega)] at h
    exact h.of_eq (by simp [bitsOf]) rfl

end ZP.Mul
