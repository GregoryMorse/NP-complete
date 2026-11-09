module

public import ZP.Tg
public import ZP.GuestCompile

@[expose] public section

/-!
# The compiled code, row by row

When every target of `D` is at most its number of states (`TgLe`), `code D pad` is
the reversal of: three `false`s, the entries of the rows of `D` in order (`rowsG`),
and `3·pad + 11` more `false`s (`code_eq`). Each entry depends only on its
position, its action and the code length `NN D pad`.
-/

namespace ZP.Cx

def entG (N p : Nat) : Act → Ent
  | .halt b => ⟨b, false, 0⟩
  | .go w r q => ⟨w, r, if p + 3 ≤ 3 * q then 3 * q - p - 2 else N + 3 * q - p - 2⟩

def rowG (N q : Nat) (r : Act × Act × Act) : List Ent :=
  [entG N (3 * q) r.1, entG N (3 * q + 1) r.2.1, entG N (3 * q + 2) r.2.2]

def rowsG (N : Nat) : Nat → List (Act × Act × Act) → List Ent
  | _, [] => []
  | q, r :: rs => rowG N q r ++ rowsG N (q + 1) rs

theorem length_rowsG (N : Nat) : ∀ (q : Nat) (rows : List (Act × Act × Act)),
    (rowsG N q rows).length = 3 * rows.length
  | _, [] => rfl
  | q, r :: rs => by
    rw [rowsG, List.length_append, length_rowsG N (q + 1) rs]
    simp [rowG]
    omega

theorem flat_app (A B : List Ent) : flat (A ++ B) = flat A ++ flat B := by
  simp [flat]

theorem r'_app : ∀ s m n : Nat, List.range' s (m + n) = List.range' s m ++ List.range' (s + m) n
  | s, 0, n => by simp
  | s, m + 1, n => by
    rw [show m + 1 + n = (m + n) + 1 by omega, List.range'_succ, List.range'_succ,
      r'_app (s + 1) m n, List.cons_append, show s + 1 + m = s + (m + 1) by omega]

section
variable (D : Mach) (pad : Nat)

theorem entOf_G {a : Act} (p : Nat) (h : tgA (nS D) a) : entOf D pad p a = entG (NN D pad) p a := by
  cases a with
  | halt b => rfl
  | go w r q =>
    have hq : q ≤ nS D := h
    show (⟨w, r, jump D pad p (3 * min q (nS D))⟩ : Ent) = _
    rw [Nat.min_eq_left hq]
    rfl

theorem entAt_row {q i : Nat} (hq : q < nS D) (hi : i < 3) :
    entAt D pad (3 * q + i) = entOf D pad (3 * q + i) (D.act q (sym i)) := by
  unfold entAt
  rw [if_pos (by omega), show (3 * q + i) / 3 = q by omega, show (3 * q + i) % 3 = i by omega]

theorem map_rowsG : ∀ (rows : List (Act × Act × Act)) (q0 : Nat), Sub D q0 rows →
    TgLe (nS D) rows → q0 + rows.length ≤ nS D →
    (List.range' (3 * q0) (3 * rows.length)).map (entAt D pad) = rowsG (NN D pad) q0 rows
  | [], _, _, _, _ => rfl
  | r :: rs, q0, hs, ht, hl => by
    simp only [List.length_cons] at hl
    have hq : q0 < nS D := by omega
    have ha : ∀ s, D.act q0 s = pick r s := by
      intro s
      have := hs.act (j := 0) (r := r) rfl s
      rwa [Nat.add_zero] at this
    have hs' : Sub D (q0 + 1) rs := (show Sub D q0 ([r] ++ rs) from hs).at rfl
    have ih := map_rowsG rs (q0 + 1) hs' ht.2 (by omega)
    rw [show 3 * (q0 + 1) = 3 * q0 + 1 + 1 + 1 by omega] at ih
    rw [List.length_cons, show 3 * (rs.length + 1) = 3 * rs.length + 1 + 1 + 1 by omega,
      List.range'_succ, List.range'_succ, List.range'_succ]
    simp only [List.map_cons, ih, rowsG, rowG]
    obtain ⟨t1, t2, t3⟩ := ht.1
    have e0 := entAt_row D pad hq (i := 0) (by omega)
    have e1 := entAt_row D pad hq (i := 1) (by omega)
    have e2 := entAt_row D pad hq (i := 2) (by omega)
    rw [Nat.add_zero] at e0
    have a0 : D.act q0 (sym 0) = r.1 := ha none
    have a1 : D.act q0 (sym 1) = r.2.1 := ha (some false)
    have a2 : D.act q0 (sym 2) = r.2.2 := ha (some true)
    rw [e0, show 3 * q0 + 1 + 1 = 3 * q0 + 2 by omega, e1, e2, a0, a1, a2,
      entOf_G D pad _ t1, entOf_G D pad _ t2, entOf_G D pad _ t3]
    rfl

def zE : Ent := ⟨false, false, 0⟩

theorem entAt_high {p : Nat} (hp : 3 * nS D ≤ p) : entAt D pad p = zE := by
  unfold entAt
  split
  · have hq : p / 3 = nS D := by omega
    rw [hq]
    have : D.act (nS D) (sym (p % 3)) = .halt false := by
      unfold Mach.act
      rw [List.getElem?_eq_none (show D.tbl.length ≤ nS D from Nat.le_refl _)]
    rw [this]
    rfl
  · rfl

theorem map_high : ∀ (n s : Nat), 3 * nS D ≤ s →
    (List.range' s n).map (entAt D pad) = List.replicate n zE
  | 0, _, _ => rfl
  | n + 1, s, h => by
    rw [List.range'_succ, List.map_cons, entAt_high D pad h, map_high n (s + 1) (by omega)]
    rfl

theorem flat_zE : ∀ n, flat (List.replicate n zE) = List.replicate (3 * n) false
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, show flat (zE :: List.replicate n zE) =
      ebits zE ++ flat (List.replicate n zE) by simp [flat], flat_zE n,
      show 3 * (n + 1) = 3 + 3 * n by omega, rep_add]
    rfl

theorem code_eq (ht : TgLe (nS D) D.tbl) :
    code D pad = (List.replicate 3 false ++ flat (rowsG (NN D pad) 0 D.tbl) ++
      List.replicate (3 * pad + 11) false).reverse := by
  have hNN : NN D pad = 3 * nS D + 5 + pad := rfl
  have hG := map_rowsG D pad D.tbl 0 (fun j r h => by rw [Nat.zero_add]; exact h) ht
    (by unfold nS; omega)
  rw [Nat.mul_zero] at hG
  have hE : ents D pad = (rowsG (NN D pad) 0 D.tbl ++ List.replicate (pad + 4) zE) ++ [zE] := by
    unfold ents
    rw [show List.range (NN D pad) = List.range' 0 (3 * D.tbl.length + (pad + 4 + 1)) by
      rw [List.range_eq_range']; congr 1; unfold nS at hNN; omega, r'_app, List.map_append, hG,
      map_high D pad (pad + 4 + 1) (0 + 3 * D.tbl.length) (by unfold nS; omega),
      List.replicate_succ', List.append_assoc]
  have hlen : (rowsG (NN D pad) 0 D.tbl ++ List.replicate (pad + 4) zE).length = NN D pad - 1 := by
    rw [List.length_append, length_rowsG, List.length_replicate]
    unfold nS at hNN
    omega
  unfold code
  rw [hE, ← hlen, rotl_split, show [zE] ++ (rowsG (NN D pad) 0 D.tbl ++
    List.replicate (pad + 4) zE) = zE :: (rowsG (NN D pad) 0 D.tbl ++
    List.replicate (pad + 4) zE) from rfl,
    show flat (zE :: (rowsG (NN D pad) 0 D.tbl ++ List.replicate (pad + 4) zE)) =
      ebits zE ++ flat (rowsG (NN D pad) 0 D.tbl ++ List.replicate (pad + 4) zE) by simp [flat],
    flat_app, flat_zE, show 3 * (pad + 4) = (3 * pad + 11) + 1 by omega, List.replicate_succ']
  simp only [← List.append_assoc, List.dropLast_concat]
  rfl

end

end ZP.Cx
