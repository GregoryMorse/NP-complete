module

public import ZP.MMEnds
public import ZP.MMSetupAll

@[expose] public section

/-! The dry row when `w` is short (`|w| ≤ m²`): the check ends with outcome 1. -/

namespace ZP.Mul.MM

open ZP

/-- The first `t` rows of length `m` of a stream. -/
def rowsOf (m : Nat) : List Nat → Nat → List (List Nat)
  | _, 0 => []
  | w, t + 1 => w.take m :: rowsOf m (w.drop m) t

theorem stor_eq : ∀ (Rws : List (List Nat)), stor Rws = Rws.flatten.reverse
  | [] => rfl
  | V :: Rws => by simp [stor, stor_eq Rws]

theorem rowsOf_length (m : Nat) : ∀ (t : Nat) (w : List Nat), (rowsOf m w t).length = t
  | 0, _ => rfl
  | t + 1, w => by simp [rowsOf, rowsOf_length m t]

theorem rowsOf_flatten (m : Nat) : ∀ (t : Nat) (w : List Nat), (rowsOf m w t).flatten = w.take (t * m)
  | 0, _ => by simp [rowsOf]
  | t + 1, w => by
    simp only [rowsOf, List.flatten_cons, rowsOf_flatten m t]
    rw [Nat.succ_mul, Nat.add_comm, List.take_add]

theorem rowsOf_mem (m : Nat) : ∀ (t : Nat) (w : List Nat), Bits w → t * m ≤ w.length →
    ∀ r ∈ rowsOf m w t, Bits r ∧ r.length = m
  | 0, _, _, _ => by simp [rowsOf]
  | t + 1, w, hw, hl => by
    intro r hr
    simp only [rowsOf, List.mem_cons] at hr
    rcases hr with rfl | hr
    · refine ⟨fun a ha => hw a (List.mem_of_mem_take ha), ?_⟩
      simp only [List.length_take]
      rw [Nat.succ_mul] at hl
      omega
    · refine rowsOf_mem m t (w.drop m) (fun a ha => hw a (List.mem_of_mem_drop ha)) ?_ r hr
      simp only [List.length_drop]
      rw [Nat.succ_mul] at hl
      omega


theorem hd_nil_hdR (q : Nat) (R : List Nat) : hd q [] R = hdR q [] (0 :: R) := by
  rw [← hd_nil0M]
  simpa using hd_snoc q [] R 0

set_option maxHeartbeats 1000000 in
theorem dryShort (m : Nat) (hm : m ≠ 0) (w : List Nat) (hw : Bits w) (hn : w.length ≤ m * m)
    (Os J sv Y2 : List Nat) (hOs : Bits Os) (hJ : Bits J) (hsv : Bits sv) (hY2 : Sym4 Y2) :
    zmmLogic.Reach (hd QMM.FA w.reverse (0 :: [] ++ 1 :: List.replicate m 3 ++ 0 :: 1 :: (Os ++ 1 :: (J ++ 1 :: (sv ++ 0 :: 1 :: Y2)))))
      (hdR Q.DP31 (1 :: (J ++ 1 :: (sv ++ [1]))) (1 :: Y2)) := by
  have h1u : (1 : Nat) ∈ ALL := by simp [ALL]
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have hT : Sym4 (Os ++ 1 :: (J ++ 1 :: (sv ++ 0 :: 1 :: Y2))) := by
    simp [sym4_app_iff, sym4_cons_iff, h0, h1u, hOs.sym4, hJ.sym4, hsv.sym4, hY2]
  have hdiv := Nat.div_add_mod w.length m
  have hmod : w.length % m < m := Nat.mod_lt _ hmpos
  have htm : w.length / m ≤ m := Nat.div_le_of_le_mul hn
  obtain ⟨t, ht⟩ : ∃ t, t = w.length / m := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = w.length % m := ⟨_, rfl⟩
  rw [← ht] at htm hdiv
  rw [← hr] at hmod hdiv
  have hnt : t * m + r = w.length := by rw [Nat.mul_comm]; exact hdiv
  have hRrem := rowsOf_mem m t w hw (by omega)
  have hstor : w.reverse = (w.drop (t * m)).reverse ++ stor (rowsOf m w t) := by
    rw [stor_eq, rowsOf_flatten, ← List.reverse_append, List.take_append_drop]
  have hF0 : Bits (w.drop (t * m)).reverse := fun a ha => hw a (List.mem_of_mem_drop (List.mem_reverse.mp ha))
  have hD := dryRows m (m - t) (rowsOf m w t) [] (w.drop (t * m)).reverse 0 hRrem hF0 (by simp)
    (by rw [rowsOf_length]; omega) _ hT
  have htm' : t + (m - t) = m := by omega
  have hD' : zmmLogic.Reach (hd QMM.FA w.reverse (0 :: [] ++ 1 :: List.replicate m 3 ++ 0 :: 1 :: (Os ++ 1 :: (J ++ 1 :: (sv ++ 0 :: 1 :: Y2)))))
      (hd QMM.FA (w.drop (t * m)).reverse (0 :: stor (rowsOf m w t) ++ 1 :: (List.replicate t 2 ++ List.replicate (m - t) 3) ++
        0 :: 1 :: (Os ++ 1 :: (J ++ 1 :: (sv ++ 0 :: 1 :: Y2))))) := by
    refine hD.of_eq ?_ ?_
    · rw [hstor, rowsOf_length, htm']; simp [stor]
    · simp [rowsOf_length]
  have hBd : Bits (stor (rowsOf m w t)) := bits_stor _ (fun r hr => (hRrem r hr).1)
  have hlenF : (w.drop (t * m)).length = r := by simp; omega
  have hrep2 : Bits (List.replicate t 2) := fun a ha => by rw [List.eq_of_mem_replicate ha]; simp [bits]
  have hrep3 : ∀ k, Bits (List.replicate k 3) := fun k a ha => by rw [List.eq_of_mem_replicate ha]; simp [bits]
  rcases hFd : (w.drop (t * m)) with _ | ⟨v, Vt⟩
  · rw [hFd] at hD'
    have hfa := endFA1 (stor (rowsOf m w t)) (List.replicate t 2 ++ List.replicate (m - t) 3) [] Os [] J sv Y2
      hBd (hrep2.app (hrep3 _)) Bits.nil hOs (by simp) hJ hsv hY2
    have hfa' : zmmLogic.Reach (hd QMM.FA [] (0 :: stor (rowsOf m w t) ++ 1 :: (List.replicate t 2 ++ List.replicate (m - t) 3) ++
        0 :: 1 :: (Os ++ 1 :: (J ++ 1 :: (sv ++ 0 :: 1 :: Y2)))))
        (hdR Q.DP31 (1 :: (J ++ 1 :: (sv ++ [1]))) (1 :: Y2)) :=
      hfa.of_eq (by rw [hd_nil_hdR]; simp) rfl
    exact hD'.trans (hfa'.of_eq (by simp) rfl)
  · rw [hFd] at hD'
    have hvb : v ∈ bits := hw v (List.mem_of_mem_drop (by rw [hFd]; simp))
    have hVt : Bits Vt := fun a ha => hw a (List.mem_of_mem_drop (by rw [hFd]; simp [ha]))
    have hrpos : 0 < r := by rw [← hlenF, hFd]; simp
    have htlt : t < m := Nat.lt_of_not_ge (fun hc => by have := Nat.mul_le_mul_right m hc; omega)
    have hVl : Vt.length + 1 = r := by rw [← hlenF, hFd]; simp
    have hrepeq : List.replicate (m - t) 3 = 3 :: List.replicate (m - t - 1) 3 := by
      rw [← List.replicate_succ]; congr 1; omega
    have hY : Bits (List.replicate (m - t - 1) 3) := hrep3 _
    have hdry := dryBad Vt.reverse (stor (rowsOf m w t)) (List.replicate t 2) (List.replicate (m - t - 1) 3) _ v
      hVt.rev hvb hBd (fun a ha => List.eq_of_mem_replicate ha) hY hT
    -- the accumulator as `acc0 ++ [x]`
    have hacc : (List.replicate t 2 ++ 2 :: List.replicate (m - t - 1) 3) ≠ [] := by simp
    obtain ⟨acc0, x, hacc0⟩ := List.eq_nil_or_concat (List.replicate t 2 ++ 2 :: List.replicate (m - t - 1) 3) |>.resolve_left hacc
    rw [List.concat_eq_append] at hacc0
    have haccB : Bits (List.replicate t 2 ++ 2 :: List.replicate (m - t - 1) 3) :=
      hrep2.app (Bits.cons (by simp [bits]) hY)
    rw [hacc0] at haccB
    have hacc0B : Bits acc0 := fun a ha => haccB a (by simp [ha])
    have hxB : x ∈ bits := haccB x (by simp)
    have hlenacc : acc0.length = m - 1 := by
      have := congrArg List.length hacc0
      simp at this; omega
    have hA : zmmLogic.Reach (hd QMM.FA (Vt.reverse ++ [v]) (0 :: stor (rowsOf m w t) ++ 1 :: (List.replicate t 2 ++ List.replicate (m - t) 3) ++
        0 :: 1 :: (Os ++ 1 :: (J ++ 1 :: (sv ++ 0 :: 1 :: Y2)))))
        (hdR QMM.J1 ([] ++ Vt.reverse) (v :: 0 :: (stor (rowsOf m w t) ++ 1 :: (acc0.reverse.reverse ++ [x] ++ 0 :: ([] ++ 1 :: (Os ++ 1 :: (J ++ 1 :: (sv ++ 0 :: 1 :: Y2)))))))) := by
      refine hdry.of_eq (by simp [hrepeq]) ?_
      rw [hd_snoc, List.reverse_reverse]
      have : List.replicate t 2 ++ 2 :: (List.replicate (m - t - 1) 3 ++ 0 :: 1 :: (Os ++ 1 :: (J ++ 1 :: (sv ++ 0 :: 1 :: Y2)))) =
          (acc0 ++ [x]) ++ 0 :: 1 :: (Os ++ 1 :: (J ++ 1 :: (sv ++ 0 :: 1 :: Y2))) := by
        rw [← hacc0]; simp
      simp only [List.nil_append, List.cons_append, List.append_assoc] at this ⊢
      rw [this]
    have pb := pbRow 1 (Or.inl rfl) (Os ++ 1 :: (J ++ 1 :: (sv ++ 0 :: 1 :: Y2))) hT Vt acc0.reverse
      (by first | (simp; omega) | simp) hVt hacc0B.rev v x hvb hxB [] (stor (rowsOf m w t)) [] Sym4.nil hBd Bits.nil
    have hRb : Bits (((x :: acc0.reverse).drop (Vt.length + 1)).reverse) := fun a ha =>
      (Bits.cons hxB hacc0B.rev) a (List.mem_of_mem_drop (List.mem_reverse.mp ha))
    have hPb : Bits ((List.zipWith (jc 1) (v :: Vt) (x :: acc0.reverse)).reverse) := fun a ha =>
      bits_zipWith 1 (v :: Vt) (x :: acc0.reverse) (Bits.cons hvb hVt) (Bits.cons hxB hacc0B.rev) a (List.mem_reverse.mp ha)
    have hend := endJ11 (Vt.reverse ++ v :: stor (rowsOf m w t)) ((((x :: acc0.reverse).drop (Vt.length + 1)).reverse))
      ((List.zipWith (jc 1) (v :: Vt) (x :: acc0.reverse)).reverse) Os [] J sv Y2
      (hVt.rev.app (Bits.cons hvb hBd)) hRb hPb hOs (by simp) hJ hsv hY2
    refine hD'.trans ?_
    simp only [List.reverse_cons]
    exact hA.trans (pb.trans (hend.of_eq (by rw [hd_nil_hdR]; simp) rfl))

end ZP.Mul.MM
