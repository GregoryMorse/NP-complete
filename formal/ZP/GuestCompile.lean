module

public import ZP.GuestTM

@[expose] public section

/-!
# A Turing machine is a guest code

The converse of `ZP/GuestTM.lean`. A machine `D` with `n` states becomes a cyclic
list of entries `w d 1^k 0`. State `j` (and the reject state `n`) owns entries
`3j, 3j+1, 3j+2`, one per symbol (blank, 0, 1). A halting action is an entry
with `k = 0`. A move to state `q'` is an entry whose `k` makes the guest skip
`k + 2` entries, landing on the block of `q'`. `pad` dummy entries make the code as
long as wanted. `compile`: the guest run of `code D pad` is the run of `D`, step for
step.
-/

namespace ZP.Cx

structure Ent where
  w : Bool
  d : Bool
  k : Nat

def ebits (e : Ent) : List Bool := e.w :: e.d :: (List.replicate e.k true ++ [false])

def flat (es : List Ent) : List Bool := es.flatMap ebits

/-! ## One entry -/

theorem rep_inj : ∀ (m k : Nat) (A B : List Bool),
    List.replicate m true ++ false :: A = List.replicate k true ++ false :: B → m = k ∧ A = B
  | 0, 0, A, B, h => ⟨rfl, by simpa using h⟩
  | 0, k + 1, A, B, h => by simp [List.replicate_succ] at h
  | m + 1, 0, A, B, h => by simp [List.replicate_succ] at h
  | m + 1, k + 1, A, B, h => by
    have h' : List.replicate m true ++ false :: A = List.replicate k true ++ false :: B := by
      simpa [List.replicate_succ] using h
    have := rep_inj m k A B h'
    exact ⟨by omega, this.2⟩

theorem rotl2_cons (a b : Bool) (X : List Bool) : rotl 2 (a :: b :: X) = X ++ [a, b] := by
  simp [rotl, rotl1_cons]

theorem ent_facts (e : Ent) (Y : List Bool) :
    entryOnes (ebits e ++ Y) = e.k ∧ rot (ebits e ++ Y) = Y ++ ebits e := by
  have h0 : false ∈ ebits e ++ Y := by simp [ebits]
  obtain ⟨m, R', e1, e2, e3⟩ := entry_split _ h0
  have e4 : rotl 2 (ebits e ++ Y) = List.replicate e.k true ++ false :: (Y ++ [e.w, e.d]) := by
    rw [show ebits e ++ Y = e.w :: e.d :: (List.replicate e.k true ++ false :: Y) by
      simp [ebits], rotl2_cons]
    simp
  rw [e4] at e1
  obtain ⟨hm, hR⟩ := rep_inj _ _ _ _ e1
  refine ⟨e2.trans hm.symm, ?_⟩
  rw [e3, ← hR, ← hm]
  simp [ebits]

theorem getD_ebits (e : Ent) (Y : List Bool) :
    (ebits e ++ Y).getD 0 false = e.w ∧ (ebits e ++ Y).getD 1 false = e.d ∧
      (ebits e ++ Y).getD 2 false = decide (e.k ≠ 0) := by
  obtain ⟨w, d, k⟩ := e
  cases k <;> simp [ebits, List.getD, List.replicate_succ]

theorem runAux_entry {T : Nat} {R : List Bool} {tape : Nat → Option Bool} {h : Nat}
    {e : Ent} {Y : List Bool} (hR : rotN (iota (tape h)) R = ebits e ++ Y) :
    runAux (T + 1) R tape h =
      if e.k = 0 then e.w
      else runAux T (rotN (e.k + 1) (Y ++ ebits e)) (write tape h e.w) (move e.d h) := by
  obtain ⟨g0, g1, g2⟩ := getD_ebits e Y
  obtain ⟨f1, f2⟩ := ent_facts e Y
  show (if (rotN (iota (tape h)) R).getD 2 false then
      runAux T (rotN (entryOnes (rotN (iota (tape h)) R) + 1) (rot (rotN (iota (tape h)) R)))
        (fun i => if i = h then some ((rotN (iota (tape h)) R).getD 0 false) else tape i)
        (if (rotN (iota (tape h)) R).getD 1 false then h + 1 else h - 1)
    else (rotN (iota (tape h)) R).getD 0 false) = _
  rw [hR, g0, g1, g2, f1, f2]
  by_cases hk : e.k = 0
  · simp [hk]
  · simp [hk]
    try rfl

/-! ## Lists of entries -/

theorem rot_flat : ∀ es : List Ent, rot (flat es) = flat (rotl1 es)
  | [] => by simp [flat, rot, rotl1]
  | e :: es => by
    have := (ent_facts e (flat es)).2
    simpa [flat, rotl1_cons] using this

theorem rotN_flat : ∀ (n : Nat) (es : List Ent), rotN n (flat es) = flat (rotl n es)
  | 0, _ => rfl
  | n + 1, es => by
    show rotN n (rot (flat es)) = flat (rotl n (rotl1 es))
    rw [rot_flat]
    exact rotN_flat n _

theorem length_rotl {α : Type} (j : Nat) (R : List α) : (rotl j R).length = R.length := by
  rw [rotl_mod]
  simp only [List.length_append, List.length_drop, List.length_take]
  have := Nat.mod_le j R.length
  omega

theorem flat_last : ∀ es : List Ent, es ≠ [] → ∃ B, flat es = B ++ [false]
  | [], h => absurd rfl h
  | [e], _ => ⟨e.w :: e.d :: List.replicate e.k true, by simp [flat, ebits]⟩
  | e :: f :: es, _ => by
    obtain ⟨B, hB⟩ := flat_last (f :: es) (by simp)
    refine ⟨ebits e ++ B, ?_⟩
    rw [show flat (e :: f :: es) = ebits e ++ flat (f :: es) by simp [flat], hB,
      List.append_assoc]

theorem flat_len : ∀ es : List Ent, 3 * es.length ≤ (flat es).length
  | [] => by simp [flat]
  | e :: es => by
    have := flat_len es
    rw [show flat (e :: es) = ebits e ++ flat es by simp [flat], List.length_append]
    have he : (ebits e).length = e.k + 3 := by simp [ebits]
    simp only [List.length_cons]
    omega

/-! ## The compiled code -/

def sym : Nat → Option Bool
  | 0 => none
  | 1 => some false
  | _ => some true

theorem sym_iota (s : Option Bool) : sym (iota s) = s := by
  cases s with
  | none => rfl
  | some b => cases b <;> rfl

theorem iota_lt (s : Option Bool) : iota s < 3 := by
  cases s with
  | none => decide
  | some b => cases b <;> decide

section
variable (D : Mach) (pad : Nat)

def nS : Nat := D.tbl.length

def NN : Nat := 3 * nS D + 5 + pad

/-- `k` for an entry at position `p` that jumps to position `p'`. -/
def jump (p p' : Nat) : Nat := if p + 3 ≤ p' then p' - p - 2 else NN D pad + p' - p - 2

def entOf (p : Nat) : Act → Ent
  | .halt b => ⟨b, false, 0⟩
  | .go w r q' => ⟨w, r, jump D pad p (3 * min q' (nS D))⟩

def entAt (p : Nat) : Ent :=
  if p < 3 * (nS D + 1) then entOf D pad p (D.act (p / 3) (sym (p % 3))) else ⟨false, false, 0⟩

def ents : List Ent := (List.range (NN D pad)).map (entAt D pad)

/-- The compiled program. -/
def code : List Bool := (flat (rotl (NN D pad - 1) (ents D pad))).dropLast.reverse

theorem act_min (q : Nat) (s : Option Bool) : D.act q s = D.act (min q (nS D)) s := by
  unfold Mach.act
  by_cases hq : q < nS D
  · rw [Nat.min_eq_left (show q ≤ nS D by omega)]
  · rw [Nat.min_eq_right (show nS D ≤ q by omega),
      List.getElem?_eq_none (show D.tbl.length ≤ q by unfold nS at hq; omega),
      List.getElem?_eq_none (show D.tbl.length ≤ nS D from Nat.le_refl _)]

theorem ents_length : (ents D pad).length = NN D pad := by simp [ents]

theorem drop_ents {p : Nat} (hp : p < NN D pad) :
    (ents D pad).drop p = entAt D pad p :: (ents D pad).drop (p + 1) := by
  rw [List.drop_eq_getElem_cons (show p < (ents D pad).length by rw [ents_length]; exact hp)]
  simp [ents]

theorem flat_rotl {p : Nat} (hp : p < NN D pad) :
    flat (rotl p (ents D pad)) =
      ebits (entAt D pad p) ++ flat ((ents D pad).drop (p + 1) ++ (ents D pad).take p) := by
  rw [rotl_mod, ents_length, Nat.mod_eq_of_lt hp, drop_ents D pad hp]
  simp [flat]

theorem rotl_NN (a : Nat) : rotl (NN D pad + a) (ents D pad) = rotl a (ents D pad) := by
  have := rotl_length (ents D pad)
  rw [ents_length] at this
  rw [Nat.add_comm, rotl_add, this]

theorem jump_spec {p p' : Nat} (hp : p + 3 ≤ NN D pad) :
    1 ≤ jump D pad p p' ∧
      (jump D pad p p' + 2 + p = p' ∨ jump D pad p p' + 2 + p = NN D pad + p') := by
  unfold jump
  split <;> omega

/-- The guest runs like `D`. -/
theorem csim : ∀ (T q : Nat) (tape : Nat → Option Bool) (h : Nat),
    runAux T (flat (rotl (3 * min q (nS D)) (ents D pad))) tape h =
      (exec D T q tape h).getD false
  | 0, _, _, _ => rfl
  | T + 1, q, tape, h => by
    have hc : min q (nS D) ≤ nS D := Nat.min_le_right _ _
    have hs := iota_lt (tape h)
    have hNN : NN D pad = 3 * nS D + 5 + pad := rfl
    obtain ⟨p, hp⟩ : ∃ p, p = 3 * min q (nS D) + iota (tape h) := ⟨_, rfl⟩
    have hpN : p < NN D pad := by omega
    have hR : rotN (iota (tape h)) (flat (rotl (3 * min q (nS D)) (ents D pad))) =
        ebits (entAt D pad p) ++ flat ((ents D pad).drop (p + 1) ++ (ents D pad).take p) := by
      rw [rotN_flat, ← rotl_add, show iota (tape h) + 3 * min q (nS D) = p by omega,
        flat_rotl D pad hpN]
    have hY : flat ((ents D pad).drop (p + 1) ++ (ents D pad).take p) ++ ebits (entAt D pad p) =
        flat (rotl (p + 1) (ents D pad)) := by
      rw [← (ent_facts _ _).2, ← flat_rotl D pad hpN, rot_flat, show p + 1 = 1 + p by omega,
        rotl_add]
      try rfl
    have hentAt : entAt D pad p = entOf D pad p (D.act q (tape h)) := by
      unfold entAt
      rw [if_pos (show p < 3 * (nS D + 1) by omega), show p / 3 = min q (nS D) by omega,
        show p % 3 = iota (tape h) by omega, sym_iota, ← act_min]
    rw [runAux_entry hR, hY, rotN_flat, ← rotl_add, exec_succ, hentAt]
    generalize D.act q (tape h) = a
    cases a with
    | halt b => simp [entOf]
    | go w r q' =>
      have hj := jump_spec D pad (p' := 3 * min q' (nS D)) (p := p) (by omega)
      have hk : ¬ (entOf D pad p (.go w r q')).k = 0 := by
        show ¬ jump D pad p _ = 0
        have := hj.1
        omega
      rw [if_neg hk]
      have e5 : rotl ((entOf D pad p (.go w r q')).k + 1 + (p + 1)) (ents D pad) =
          rotl (3 * min q' (nS D)) (ents D pad) := by
        show rotl (jump D pad p (3 * min q' (nS D)) + 1 + (p + 1)) _ = _
        rcases hj.2 with h1 | h1
        · rw [show jump D pad p (3 * min q' (nS D)) + 1 + (p + 1) = 3 * min q' (nS D) by omega]
        · rw [show jump D pad p (3 * min q' (nS D)) + 1 + (p + 1) =
            NN D pad + 3 * min q' (nS D) by omega, rotl_NN]
      rw [e5]
      exact csim T q' _ _

theorem code_rev : (code D pad).reverse ++ [false] = flat (rotl (NN D pad - 1) (ents D pad)) := by
  have hne : rotl (NN D pad - 1) (ents D pad) ≠ [] := by
    intro e
    have := congrArg List.length e
    rw [length_rotl, ents_length] at this
    simp [NN] at this
  obtain ⟨B, hB⟩ := flat_last _ hne
  unfold code
  rw [List.reverse_reverse, hB, List.dropLast_concat]

theorem code_length : pad ≤ (code D pad).length := by
  have := flat_len (rotl (NN D pad - 1) (ents D pad))
  rw [length_rotl, ents_length] at this
  have hNN : NN D pad = 3 * nS D + 5 + pad := rfl
  unfold code
  rw [List.length_reverse, List.length_dropLast]
  omega

theorem compile_spec (x : List Bool) (T : Nat) :
    run (code D pad) x T = (exec D T 0 (inTape x) 0).getD false := by
  have e : rotl1 (rotl (NN D pad - 1) (ents D pad)) = rotl (3 * min 0 (nS D)) (ents D pad) := by
    rw [show 3 * min 0 (nS D) = 0 by simp]
    show rotl 1 _ = _
    have hNN : NN D pad = 3 * nS D + 5 + pad := rfl
    rw [← rotl_add, show 1 + (NN D pad - 1) = NN D pad + 0 by omega, rotl_NN]
  show runAux T (rot ((code D pad).reverse ++ [false])) (inTape x) 0 = _
  rw [code_rev, rot_flat, e]
  exact csim D pad T 0 (inTape x) 0

end

/-- Every machine is a guest code, of any length at least `pad`. -/
theorem compile (D : Mach) (pad : Nat) : ∃ P : List Bool, pad ≤ P.length ∧
    ∀ x T, run P x T = (exec D T 0 (inTape x) 0).getD false :=
  ⟨code D pad, code_length D pad, compile_spec D pad⟩

end ZP.Cx
