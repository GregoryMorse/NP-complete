module

public import ZP.CheckG2

@[expose] public section

/-! # The check phase of the GI machine (part 3): the `H` region with `c` passed entries -/

namespace ZP.G

open ZP

/-- The tape of `H` (entry tails `hs`, first cells `3`) in which the first `c` entries are passed
(first cell marked).  Entries are separated by `M`; the last one is followed by the blank. -/
def HP : List (List Nat) → Nat → List Nat
  | [], _ => []
  | [t], c => (if 0 < c then 2 else 3) :: t
  | t :: u :: ts, c => (if 0 < c then 2 else 3) :: (t ++ 1 :: HP (u :: ts) (c - 1))

theorem HP_sym4 : ∀ (hs : List (List Nat)) (c : Nat), (∀ t ∈ hs, Bits t) → Sym4 (HP hs c)
  | [], _, _ => Sym4.nil
  | [t], c, h => by
    have ht := h t (List.mem_cons_self ..)
    refine Sym4.cons ?_ ht.sym4
    split <;> simp [ALL]
  | t :: u :: ts, c, h => by
    have ht := h t (List.mem_cons_self ..)
    have := HP_sym4 (u :: ts) (c - 1) (fun s hs => h s (List.mem_cons_of_mem _ hs))
    refine Sym4.cons ?_ (ht.sym4.app (Sym4.cons (by simp [ALL]) this))
    split <;> simp [ALL]

theorem HP_split : ∀ (hs : List (List Nat)) (c : Nat), c < hs.length →
    ∃ Rest0 : List Nat, HP hs c = MP (hs.take c) ++ 3 :: Rest0 ∧ HP hs (c + 1) = MP (hs.take c) ++ 2 :: Rest0
  | [], c, h => by simp at h
  | [t], c, h => by
    have : c = 0 := by simp at h; omega
    subst this
    exact ⟨t, by simp [HP, MP], by simp [HP, MP]⟩
  | t :: u :: ts, 0, h => ⟨t ++ 1 :: HP (u :: ts) 0, by simp [HP, MP], by simp [HP, MP]⟩
  | t :: u :: ts, c + 1, h => by
    obtain ⟨R0, h1, h2⟩ := HP_split (u :: ts) c (by simp at h ⊢; omega)
    refine ⟨R0, ?_, ?_⟩
    · simp [HP, MP, h1]
    · simp [HP, MP, h2]

theorem HP_full : ∀ (hs : List (List Nat)), hs ≠ [] →
    ∃ tl, HP hs hs.length = MP hs.dropLast ++ 2 :: tl ∧ hs.getLast? = some tl
  | [], h => absurd rfl h
  | [t], _ => ⟨t, by simp [HP, MP], by simp⟩
  | t :: u :: ts, _ => by
    obtain ⟨tl, h1, h2⟩ := HP_full (u :: ts) (by simp)
    refine ⟨tl, ?_, ?_⟩
    · simp [HP, MP, h1]
      exact h1
    · simpa using h2

/-- Skip one `H` entry: walk to `H`, pass the passed entries, mark the first cell of the next one. -/
theorem hSkipG (P cb mb Rest0 : List Nat) (ws xs pasT : List (List Nat))
    (hcb : Bits cb) (hws : ∀ e ∈ ws, Bits e ∧ e ≠ []) (hmb : Bits mb) (hxs : ∀ e ∈ xs, Bits e ∧ e ≠ [])
    (hpas : ∀ t ∈ pasT, Bits t) (hP : Sym4 P) (hR : Sym4 Rest0) :
    zgiLogic.Reach
      (hdR QG.gN1 P (cb ++ 1 :: (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (MP pasT ++ 3 :: Rest0))))))
      (hd QG.gIL0 (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1] ++ MEs xs ++ [1] ++ MP pasT)
        (2 :: Rest0)) := by
  have sW := MEs_sym4 ws (fun e he => (hws e he).1)
  have sX := MEs_sym4 xs (fun e he => (hxs e he).1)
  have sP := MP_sym4 pasT hpas
  have s0 : Sym4 Rest0 := hR
  have s1 : Sym4 (MP pasT ++ 3 :: Rest0) := by simp [ALL, sP, s0]
  have s2 : Sym4 (MEs xs ++ 1 :: (MP pasT ++ 3 :: Rest0)) := by simp [ALL, sX, s1]
  have s3 : Sym4 (mb ++ 1 :: (MEs xs ++ 1 :: (MP pasT ++ 3 :: Rest0))) := by simp [ALL, hmb.sym4, s2]
  have s4 : Sym4 (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (MP pasT ++ 3 :: Rest0)))) := by simp [ALL, sW, s3]
  have hA := wn1Cells _ s4 cb P hcb hP
  have hB := wn1Walk _ s3 ws (P ++ cb ++ [1]) hws (by simp [ALL, hP, hcb.sym4])
  have hC := wn2Cells _ s2 mb (P ++ cb ++ [1] ++ MEs ws ++ [1]) hmb (by simp [ALL, hP, hcb.sym4, sW])
  have hD := wn2Walk _ s1 xs (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1]) hxs (by simp [ALL, hP, hcb.sym4, sW, hmb.sym4])
  have hE := s3Walk (3 :: Rest0) (by simp [ALL, s0]) pasT (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1] ++ MEs xs ++ [1]) hpas (by simp [ALL, hP, hcb.sym4, sW, hmb.sym4, sX])
  have hF := s3Mark (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1] ++ MEs xs ++ [1] ++ MP pasT) Rest0
    (by simp [ALL, hP, hcb.sym4, sW, hmb.sym4, sX, sP]) s0
  exact (hA.of_eq rfl rfl).trans ((hB.of_eq rfl rfl).trans ((hC.of_eq rfl rfl).trans ((hD.of_eq rfl rfl).trans
    ((hE.of_eq rfl rfl).trans (hF.of_eq rfl rfl)))))

theorem s4Walk (R : List Nat) (hR : Sym4 R) : ∀ (c P : List Nat), Bits c → Sym4 P →
    zgiLogic.Reach (hdR QG.gS4 P (c ++ R)) (hdR QG.gS4 (P ++ c) R)
  | [], P, _, _ => by simpa using (LTM.Reach.refl _ _)
  | b :: c, P, hc, hP => by
    have hb := hc b (List.mem_cons_self ..)
    have hc' : Bits c := fun a ha => hc a (List.mem_cons_of_mem _ ha)
    have h1 := s4Cell P (c ++ R) b hb hP (by simp [ALL, hR, hc'.sym4])
    have hP' : Sym4 (P ++ [b]) := by
      rcases mem_bits hb with rfl | rfl <;> simp [ALL, hP]
    have h2 := s4Walk R hR c (P ++ [b]) hc' hP'
    exact (h1.of_eq rfl rfl).trans (h2.of_eq rfl (by simp))

theorem s4Fail (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gS4 P (0 :: R)) (hd QG.gFG P (0 :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 0, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 0, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- A skip when every entry of `H` is already passed (the last one ends at the blank): failure. -/
theorem hSkipFail (P cb mb tl Z : List Nat) (ws xs pasT : List (List Nat))
    (hcb : Bits cb) (hws : ∀ e ∈ ws, Bits e ∧ e ≠ []) (hmb : Bits mb) (hxs : ∀ e ∈ xs, Bits e ∧ e ≠ [])
    (hpas : ∀ t ∈ pasT, Bits t) (htl : Bits tl) (hP : Sym4 P) (hZ : Sym4 Z) :
    zgiLogic.Reach
      (hdR QG.gN1 P (cb ++ 1 :: (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (MP pasT ++ 2 :: (tl ++ 0 :: Z)))))))
      (hd QG.gFG (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1] ++ MEs xs ++ [1] ++ MP pasT ++ [2] ++ tl)
        (0 :: Z)) := by
  have sW := MEs_sym4 ws (fun e he => (hws e he).1)
  have sX := MEs_sym4 xs (fun e he => (hxs e he).1)
  have sP := MP_sym4 pasT hpas
  have s0 : Sym4 (tl ++ 0 :: Z) := by simp [ALL, htl.sym4, hZ]
  have s1 : Sym4 (MP pasT ++ 2 :: (tl ++ 0 :: Z)) := by simp [ALL, sP, s0]
  have s2 : Sym4 (MEs xs ++ 1 :: (MP pasT ++ 2 :: (tl ++ 0 :: Z))) := by simp [ALL, sX, s1]
  have s3 : Sym4 (mb ++ 1 :: (MEs xs ++ 1 :: (MP pasT ++ 2 :: (tl ++ 0 :: Z)))) := by simp [ALL, hmb.sym4, s2]
  have s4 : Sym4 (MEs ws ++ 1 :: (mb ++ 1 :: (MEs xs ++ 1 :: (MP pasT ++ 2 :: (tl ++ 0 :: Z))))) := by simp [ALL, sW, s3]
  have hA := wn1Cells _ s4 cb P hcb hP
  have hB := wn1Walk _ s3 ws (P ++ cb ++ [1]) hws (by simp [ALL, hP, hcb.sym4])
  have hC := wn2Cells _ s2 mb (P ++ cb ++ [1] ++ MEs ws ++ [1]) hmb (by simp [ALL, hP, hcb.sym4, sW])
  have hD := wn2Walk _ s1 xs (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1]) hxs (by simp [ALL, hP, hcb.sym4, sW, hmb.sym4])
  have hE := s3Walk (2 :: (tl ++ 0 :: Z)) (by simp [ALL, s0]) pasT (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1] ++ MEs xs ++ [1]) hpas (by simp [ALL, hP, hcb.sym4, sW, hmb.sym4, sX])
  have hF := s3Passed (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1] ++ MEs xs ++ [1] ++ MP pasT) (tl ++ 0 :: Z)
    (by simp [ALL, hP, hcb.sym4, sW, hmb.sym4, sX, sP]) s0
  have hG := s4Walk (0 :: Z) (by simp [ALL, hZ]) tl (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1] ++ MEs xs ++ [1] ++ MP pasT ++ [2]) htl
    (by simp [ALL, hP, hcb.sym4, sW, hmb.sym4, sX, sP])
  have hH := s4Fail (P ++ cb ++ [1] ++ MEs ws ++ [1] ++ mb ++ [1] ++ MEs xs ++ [1] ++ MP pasT ++ [2] ++ tl) Z
    (by simp [ALL, hP, hcb.sym4, sW, hmb.sym4, sX, sP, htl.sym4]) hZ
  exact (hA.of_eq rfl rfl).trans ((hB.of_eq rfl rfl).trans ((hC.of_eq rfl rfl).trans ((hD.of_eq rfl rfl).trans
    ((hE.of_eq rfl rfl).trans ((hF.of_eq rfl rfl).trans ((hG.of_eq rfl rfl).trans (hH.of_eq rfl rfl)))))))

end ZP.G
