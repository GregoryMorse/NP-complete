module

public import ZP.Gen

@[expose] public section

/-!
# The code generator

`GEN V k m E` turns `x` (on stack 0) into `code (DX V k m x) pad` with
`pad = (|x| + 2) ^ E` (`gen_ok`). It builds `pad` and `NN` in unary, writes three
`false`s, the static rows (`genRows`), two rows per bit of `x` (`XL`), the two final
rows (`XEND`), `3·pad + 11` more `false`s, and moves the result to stack 0.
-/

namespace ZP.Cx

/-! ## Total length -/

def tl (S : List (List Bool)) : Nat := (S.map List.length).sum

theorem tl_set : ∀ (S : List (List Bool)) (i : Nat) (v : List Bool),
    tl (S.set i v) + (S.getD i []).length ≤ tl S + v.length
  | [], _, _ => by simp [tl]
  | a :: S, 0, v => by simp [tl]; omega
  | a :: S, i + 1, v => by
    have := tl_set S i v
    simp only [tl, List.set_cons_succ, List.map_cons, List.sum_cons, List.getD_cons_succ] at this ⊢
    omega

theorem Exec.tl_le {c : Cmd} {S S' : List (List Bool)} {t : Nat} (h : Exec c S S' t) :
    tl S' ≤ tl S + t := by
  induction h with
  | @push i b S =>
    have := tl_set S i (b :: S.getD i [])
    simp only [List.length_cons] at this
    omega
  | @pop i S =>
    have := tl_set S i (S.getD i []).tail
    simp only [List.length_tail] at this
    omega
  | cs _ ih => omega
  | seq _ _ ih1 ih2 => omega
  | whT _ _ _ ih1 ih2 => omega
  | whF _ => omega
  | skip => omega

theorem tg_left {B : Nat} : ∀ (A C : List (Act × Act × Act)), TgLe B (A ++ C) → TgLe B A
  | [], _, _ => trivial
  | _ :: A, C, h => ⟨h.1, tg_left A C h.2⟩

theorem rowsG_app (N : Nat) : ∀ (q : Nat) (A C : List (Act × Act × Act)),
    rowsG N q (A ++ C) = rowsG N q A ++ rowsG N (q + A.length) C
  | q, [], C => by simp [rowsG]
  | q, r :: A, C => by
    show rowG N q r ++ rowsG N (q + 1) (A ++ C) = (rowG N q r ++ rowsG N (q + 1) A) ++ _
    rw [rowsG_app N (q + 1) A C, List.append_assoc, List.length_cons,
      show q + 1 + A.length = q + (A.length + 1) by omega]

/-! ## Input rows -/

theorem entG_back {N p : Nat} {w r : Bool} {q : Nat} (h : 3 * q ≤ p + 2) :
    entG N p (.go w r q) = ⟨w, r, N + 3 * q - p - 2⟩ := by
  simp only [entG, show ¬ (p + 3 ≤ 3 * q) by omega, ↓reduceIte]

theorem eG_A (N f : Nat) : entG N (3 * f + 2) (.go true true (f + 1)) = ⟨true, true, N - 1⟩ := by
  rw [entG_back (by omega)]; congr 1; omega

theorem eG_Bf (N f : Nat) :
    entG N (3 * (f + 1) + 1) (.go false true (f + 2)) = ⟨false, true, N⟩ := by
  rw [entG_back (by omega)]; congr 1; omega

theorem eG_Bt (N f : Nat) :
    entG N (3 * (f + 1) + 2) (.go true true (f + 2)) = ⟨true, true, N - 1⟩ := by
  rw [entG_back (by omega)]; congr 1; omega

theorem eG_E1 (N f : Nat) : entG N (3 * f + 1) (.go false true (f + 1)) = ⟨false, true, N⟩ := by
  rw [entG_back (by omega)]; congr 1; omega

theorem eG_E2 (N f : Nat) : entG N (3 * (f + 1) + 2) (.go true false 1) =
    ⟨true, false, N + 3 * 1 - (3 * (f + 1) + 2) - 2⟩ := entG_back (by omega)

def xbE (N : Nat) (b : Bool) : List Ent :=
  [zE, zE, ⟨true, true, N - 1⟩] ++
    (if b then [zE, zE, ⟨true, true, N - 1⟩] else [zE, ⟨false, true, N⟩, zE])

theorem xb_rows (N f : Nat) (b : Bool) :
    rowG N f (H, H, .go true true (f + 1)) ++ rowG N (f + 1) (bitRow b (f + 2)) = xbE N b := by
  cases b
  · show [entG N (3 * f) H, entG N (3 * f + 1) H, entG N (3 * f + 2) (.go true true (f + 1))] ++
      [entG N (3 * (f + 1)) H, entG N (3 * (f + 1) + 1) (.go false true (f + 2)),
        entG N (3 * (f + 1) + 2) H] = _
    rw [eG_A, eG_Bf] <;> rfl
  · show [entG N (3 * f) H, entG N (3 * f + 1) H, entG N (3 * f + 2) (.go true true (f + 1))] ++
      [entG N (3 * (f + 1)) H, entG N (3 * (f + 1) + 1) H,
        entG N (3 * (f + 1) + 2) (.go true true (f + 2))] = _
    rw [eG_A, eG_Bt] <;> rfl

theorem xrows_G (N : Nat) : ∀ (x : List Bool) (f : Nat),
    rowsG N f (xrows f 1 x) =
      x.flatMap (xbE N) ++ rowsG N (f + 2 * x.length) (xrows (f + 2 * x.length) 1 [])
  | [], f => by simp
  | b :: x, f => by
    have e : rowsG N f (xrows f 1 (b :: x)) =
        (rowG N f (H, H, .go true true (f + 1)) ++ rowG N (f + 1) (bitRow b (f + 2))) ++
          rowsG N (f + 2) (xrows (f + 2) 1 x) := by
      rw [List.append_assoc]; rfl
    rw [e, xb_rows, xrows_G N x (f + 2), List.flatMap_cons, List.append_assoc,
      show f + 2 + 2 * x.length = f + 2 * (b :: x).length by simp only [List.length_cons]; omega]

theorem xend_eq {N g P : Nat} (h : N = 3 * g + P + 11) :
    rowsG N g (xrows g 1 []) = [zE, ⟨false, true, N⟩, zE, zE, zE, ⟨true, false, P + 7⟩] := by
  show [entG N (3 * g) H, entG N (3 * g + 1) (.go false true (g + 1)), entG N (3 * g + 2) H] ++
    ([entG N (3 * (g + 1)) H, entG N (3 * (g + 1) + 1) H,
      entG N (3 * (g + 1) + 2) (.go true false 1)] ++ []) = _
  rw [eG_E1, eG_E2, show N + 3 * 1 - (3 * (g + 1) + 2) - 2 = P + 7 by omega] <;> rfl

/-! ## Emitting the input rows -/

def eZ : Cmd := eW false false .skip
def eN (w d : Bool) : Cmd := eW w d NNc
def eN1 (w d : Bool) : Cmd := eW w d (.seq NNc (popK 1 1))

def XB (b : Bool) : Cmd :=
  .seq eZ (.seq eZ (.seq (eN1 true true) (if b then .seq eZ (.seq eZ (eN1 true true))
    else .seq eZ (.seq (eN false true) eZ))))

def XL : Cmd := .wh 0 false true true (.cs 0 .skip (.seq (.pop 0) (XB false)) (.seq (.pop 0) (XB true)))

def XEND : Cmd :=
  .seq eZ (.seq (eN false true) (.seq eZ (.seq eZ (.seq eZ (eW true false (.seq PADc (pushK 1 7)))))))

def TR1 : Cmd :=
  .wh 4 false true true (.seq (.pop 4) (.seq (.push 1 false) (.seq (.push 1 false) (.push 1 false))))

section
variable {N P : Nat}

theorem em_eZ : Em N P eZ [zE] 4 := em_eW body_skip

theorem em_eN (w d : Bool) : Em N P (eN w d) [⟨w, d, N⟩] (8 * N + 5) := em_eW body_NNc

theorem em_eN1 (h : 1 ≤ N) (w d : Bool) : Em N P (eN1 w d) [⟨w, d, N - 1⟩] (9 * N + 6) :=
  em_eW (body_NNpop h)

theorem em_XB (h : 1 ≤ N) : ∀ b, Em N P (XB b) (xbE N b) (54 * N + 40)
  | false => ((em_eZ).seq ((em_eZ).seq ((em_eN1 h true true).seq
      ((em_eZ).seq ((em_eN false true).seq em_eZ))))).cast rfl (by omega)
  | true => ((em_eZ).seq ((em_eZ).seq ((em_eN1 h true true).seq
      ((em_eZ).seq ((em_eZ).seq (em_eN1 h true true)))))).cast rfl (by omega)

theorem xl_ok (h : 1 ≤ N) : ∀ (x O : List Bool), ExecB XL (ES x O N P)
    (ES [] ((flat (x.flatMap (xbE N))).reverse ++ O) N P) (x.length * (54 * N + 43) + 1)
  | [], O => (ExecB.whF rfl).to rfl (by simp)
  | b :: x, O => by
    have e1 : ExecB (.cs 0 .skip (.seq (.pop 0) (XB false)) (.seq (.pop 0) (XB true)))
        (ES (b :: x) O N P) (ES x ((flat (xbE N b)).reverse ++ O) N P) (54 * N + 42) := by
      cases b
      · have hb : ExecB (.seq (.pop 0) (XB false)) (ES (false :: x) O N P)
            (ES x ((flat (xbE N false)).reverse ++ O) N P) (1 + (54 * N + 40)) :=
          ((ExecB.pop (i := 0) (S := ES (false :: x) O N P)).to (S2 := ES x O N P) rfl
            (Nat.le_refl _)).seq (em_XB h false x O)
        exact (ExecB.cs (i := 0) (pe := .skip) (pf := .seq (.pop 0) (XB false))
          (pt := .seq (.pop 0) (XB true)) hb).to rfl (by omega)
      · have hb : ExecB (.seq (.pop 0) (XB true)) (ES (true :: x) O N P)
            (ES x ((flat (xbE N true)).reverse ++ O) N P) (1 + (54 * N + 40)) :=
          ((ExecB.pop (i := 0) (S := ES (true :: x) O N P)).to (S2 := ES x O N P) rfl
            (Nat.le_refl _)).seq (em_XB h true x O)
        exact (ExecB.cs (i := 0) (pe := .skip) (pf := .seq (.pop 0) (XB false))
          (pt := .seq (.pop 0) (XB true)) hb).to rfl (by omega)
    have e2 := xl_ok h x ((flat (xbE N b)).reverse ++ O)
    refine (ExecB.whT (by cases b <;> rfl) e1 e2).to ?_ ?_
    · rw [List.flatMap_cons, flat_app, List.reverse_append, List.append_assoc]
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      generalize x.length * (54 * N + 43) = Z
      omega

theorem em_XEND : Em N P XEND [zE, ⟨false, true, N⟩, zE, zE, zE, ⟨true, false, P + 7⟩]
    (8 * N + 8 * P + 42) :=
  ((em_eZ).seq ((em_eN false true).seq ((em_eZ).seq ((em_eZ).seq ((em_eZ).seq
    (em_eW (w := true) (d := false) body_PAD7)))))).cast rfl (by omega)

theorem tr_ok : ∀ (P : Nat) (X O : List Bool), ExecB TR1 (ES X O N P)
    (ES X (List.replicate (3 * P) false ++ O) N 0) (5 * P + 1)
  | 0, X, O => (ExecB.whF rfl).to rfl (Nat.le_refl _)
  | P + 1, X, O => by
    have e1 : ExecB (.seq (.pop 4) (.seq (.push 1 false) (.seq (.push 1 false) (.push 1 false))))
        (ES X O N (P + 1)) (ES X (false :: false :: false :: O) N P) 4 :=
      (ExecB.pop.seq (ExecB.push.seq (ExecB.push.seq ExecB.push))).to rfl (Nat.le_refl _)
    have e2 := tr_ok P X (false :: false :: false :: O)
    refine (ExecB.whT rfl e1 e2).to ?_ (by omega)
    rw [rep_snoc, rep_snoc, rep_snoc, show 3 * (P + 1) = 3 * P + 1 + 1 + 1 by omega]

end

/-! ## The generator -/

def GEN (V : Mach) (k m E : Nat) : Cmd :=
  .seq (CLK E) (.seq (dup 3 2 4) (.seq (addk 5 2 6) (.seq (pushK 2 (3 * F0 V k m - 1))
  (.seq eZ (.seq (genRows 0 (fxRows V k m)) (.seq XL (.seq XEND (.seq TR1
  (.seq (pushB 1 false 11) (.seq (clr 2) (.seq (mv 1 6) (mv 6 0))))))))))))

theorem ok_pushB (b : Bool) : ∀ n, Ok 8 (pushB 1 b n)
  | 0 => trivial
  | n + 1 => ⟨show 1 < 8 by decide, ok_pushB b n⟩

theorem ok_GEN (V : Mach) (k m E : Nat) : Ok 8 (GEN V k m E) :=
  ⟨ok_CLK E, okb_ok 8 (dup 3 2 4) (by decide), ⟨show 5 < 8 by decide, show 5 < 8 by decide,
    ok_pushK (by decide) 6⟩, ok_pushK (by decide) _, okb_ok 8 eZ (by decide),
    ok_genRows _ _, okb_ok 8 XL (by decide), okb_ok 8 XEND (by decide), okb_ok 8 TR1 (by decide),
    ok_pushB false 11, okb_ok 8 (clr 2) (by decide), okb_ok 8 (mv 1 6) (by decide),
    okb_ok 8 (mv 6 0) (by decide)⟩

def genT (n pad N F PB : Nat) : Nat :=
  10 * n + 5 + PB + (4 * pad + 1) + ((n + 2) * 9 + 1) + 3 * F + 4 + (F * (27 * N + 21) + 1) +
    (n * (54 * N + 43) + 1) + (8 * N + 8 * pad + 42) + (5 * pad + 1) + 12 + (2 * N + 1)

def genB (V : Mach) (k m E n : Nat) : Nat :=
  9 * genT n ((n + 2) ^ E) (3 * F0 V k m + 6 * n + 11 + (n + 2) ^ E) (F0 V k m) (powB (n + 2) E) +
    8 * n + 2

theorem tl_WS (a b c d e f g h : List Bool) :
    tl (WS a b c d e f g h) = a.length + b.length + c.length + d.length + e.length + f.length +
      g.length + h.length := by
  simp [tl, WS]; omega

theorem gen_ok (V : Mach) (k m E : Nat) (x : List Bool) :
    ExecB (GEN V k m E) (WS x [] [] [] [] [] [] [])
      (WS (code (DX V k m x) ((x.length + 2) ^ E)) [] [] [] [] [] [] []) (genB V k m E x.length) := by
  obtain ⟨n, hn⟩ : ∃ n, n = x.length := ⟨_, rfl⟩
  obtain ⟨pad, hpad⟩ : ∃ pad, pad = (x.length + 2) ^ E := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, F = F0 V k m := ⟨_, rfl⟩
  have hF68 : 68 ≤ F := by rw [hF]; unfold F0; omega
  obtain ⟨N, hN⟩ : ∃ N, N = NN (DX V k m x) pad := ⟨_, rfl⟩
  have hNv : N = 3 * F + 6 * n + 11 + pad := by
    rw [hN]; unfold NN nS; rw [length_DX, ← hF, ← hn]; omega
  -- stage 1: clock
  have s1 := clk_ok (L := []) x E
  rw [← hpad, ← hn] at s1
  -- stage 2: copy pad to stacks 2 and 4
  have s2 := (dup_ok (i := 3) (j := 2) (l := 4) (by decide) (by decide) (by decide) pad
    (WS x [] [] (List.replicate pad true) [] (List.replicate (n + 2) true) [] [])
    (by simp [WS]) (by simp [WS]) (by simp [WS]) rfl).to (S2 := WS x [] (List.replicate pad true)
      [] (List.replicate pad true) (List.replicate (n + 2) true) [] []) (by simp [WS])
      (Nat.le_refl _)
  -- stage 3: add 6 per unit of n + 2
  have s3 := (addk_ok (i := 5) (j := 2) (K := 6) (by decide) (n + 2)
    (WS x [] (List.replicate pad true) [] (List.replicate pad true) (List.replicate (n + 2) true)
      [] []) (by simp [WS]) (by simp [WS]) rfl).to
    (S2 := WS x [] (List.replicate ((n + 2) * 6) true ++ List.replicate pad true) []
      (List.replicate pad true) [] [] []) (by simp [WS]) (Nat.le_refl _)
  -- stage 4: the rest of NN
  have hNN : List.replicate (3 * F0 V k m - 1) true ++
      (List.replicate ((n + 2) * 6) true ++ List.replicate pad true) = List.replicate N true := by
    rw [← rep_add, ← rep_add]; congr 1; omega
  have s4 := (pushK_gen (i := 2) (3 * F0 V k m - 1)
    (WS x [] (List.replicate ((n + 2) * 6) true ++ List.replicate pad true) []
      (List.replicate pad true) [] [] []) (by simp [WS])).to (S2 := ES x [] N pad)
    (by
      show WS x [] (List.replicate (3 * F0 V k m - 1) true ++
        (List.replicate ((n + 2) * 6) true ++ List.replicate pad true)) []
        (List.replicate pad true) [] [] [] = _
      rw [hNN]; rfl) (Nat.le_refl _)
  -- stages 5-8: emission
  have hN1 : 1 ≤ N := by omega
  have s5 := (em_eZ (N := N) (P := pad)) x []
  have htg : TgLe (DX V k m x).tbl.length (fxRows V k m) :=
    tg_left _ _ (tg_DX V k m x)
  have hlen : (DX V k m x).tbl.length = F + 2 * n + 2 := by rw [length_DX, ← hF, ← hn]
  have s6 := em_genRows (N := N) (P := pad) (B := (DX V k m x).tbl.length) (by omega)
    (fxRows V k m) 0 htg (by rw [length_fxRows, ← hF]; omega) x ((flat [zE]).reverse ++ [])
  have s7 := xl_ok (P := pad) hN1 x
    ((flat (rowsG N 0 (fxRows V k m))).reverse ++ ((flat [zE]).reverse ++ []))
  have s8 := (em_XEND (N := N) (P := pad)) []
    ((flat (x.flatMap (xbE N))).reverse ++
      ((flat (rowsG N 0 (fxRows V k m))).reverse ++ ((flat [zE]).reverse ++ [])))
  generalize hO8 : (flat [zE, ⟨false, true, N⟩, zE, zE, zE, ⟨true, false, pad + 7⟩]).reverse ++
    ((flat (x.flatMap (xbE N))).reverse ++
      ((flat (rowsG N 0 (fxRows V k m))).reverse ++ ((flat [zE]).reverse ++ []))) = O8 at s8
  -- stages 9-10: trailing falses
  have s9 := tr_ok (N := N) pad [] O8
  have s10 := (pushB_gen (i := 1) false 11 (ES [] (List.replicate (3 * pad) false ++ O8) N 0)
    (by simp [ES, WS])).to (S2 := ES [] (List.replicate 11 false ++
      (List.replicate (3 * pad) false ++ O8)) N 0) rfl (Nat.le_refl _)
  generalize hO10 : List.replicate 11 false ++ (List.replicate (3 * pad) false ++ O8) = O10 at s10
  -- stages 11-13: clean up
  have s11 := (clr_ok (i := 2) (List.replicate N true) (ES [] O10 N 0) (by simp [ES, WS]) rfl).to
    (S2 := WS [] O10 [] [] [] [] [] []) rfl (Nat.le_refl _)
  have s12 := (mv_ok (i := 1) (j := 6) (by decide) O10 (WS [] O10 [] [] [] [] [] [])
    (by simp [WS]) (by simp [WS]) rfl).to (S2 := WS [] [] [] [] [] [] O10.reverse [])
    (by simp [WS]) (Nat.le_refl _)
  have s13 := (mv_ok (i := 6) (j := 0) (by decide) O10.reverse (WS [] [] [] [] [] [] O10.reverse [])
    (by simp [WS]) (by simp [WS]) rfl).to (S2 := WS O10 [] [] [] [] [] [] [])
    (by simp [WS]) (Nat.le_refl _)
  -- the output is the code
  have hcode : O10 = code (DX V k m x) pad := by
    rw [code_eq (DX V k m x) pad (tg_DX V k m x), ← hN,
      show (DX V k m x).tbl = fxRows V k m ++ xrows (F0 V k m) 1 x from rfl, rowsG_app,
      length_fxRows, Nat.zero_add, xrows_G, xend_eq (g := F0 V k m + 2 * x.length) (P := pad)
      (by rw [← hF, ← hn]; omega), ← hO10, ← hO8]
    simp only [flat_app, List.reverse_append, List.append_assoc, List.reverse_replicate,
      rep_add false (3 * pad) 11, List.append_nil]
    rfl
  rw [← hpad, ← hcode]
  -- the time bound
  obtain ⟨t1, h1, E1⟩ := s1
  obtain ⟨t2, h2, E2⟩ := s2
  obtain ⟨t3, h3, E3⟩ := s3
  obtain ⟨t4, h4, E4⟩ := s4
  obtain ⟨t5, h5, E5⟩ := s5
  obtain ⟨t6, h6, E6⟩ := s6
  obtain ⟨t7, h7, E7⟩ := s7
  obtain ⟨t8, h8, E8⟩ := s8
  obtain ⟨t9, h9, E9⟩ := s9
  obtain ⟨t10, h10, E10⟩ := s10
  obtain ⟨t11, h11, E11⟩ := s11
  obtain ⟨t12, h12, E12⟩ := s12
  obtain ⟨t13, h13, E13⟩ := s13
  have l1 := E1.tl_le
  have l2 := E2.tl_le
  have l3 := E3.tl_le
  have l4 := E4.tl_le
  have l5 := E5.tl_le
  have l6 := E6.tl_le
  have l7 := E7.tl_le
  have l8 := E8.tl_le
  have l9 := E9.tl_le
  have l10 := E10.tl_le
  have l11 := E11.tl_le
  have g0 : tl (WS x [] [] [] [] [] [] []) = n := by rw [tl_WS]; simp [hn]
  have g11 : tl (WS [] O10 [] [] [] [] [] []) = O10.length := by rw [tl_WS]; simp
  refine ⟨_, ?_, E1.seq (E2.seq (E3.seq (E4.seq (E5.seq (E6.seq (E7.seq (E8.seq (E9.seq
    (E10.seq (E11.seq (E12.seq E13)))))))))))⟩
  simp only [List.length_reverse, List.length_replicate, length_fxRows] at h12 h13 h11 h2 h6
  rw [g0] at l1
  rw [g11] at l11
  have hG : genB V k m E x.length = 9 * genT n pad N F (powB (n + 2) E) + 8 * n + 2 := by
    unfold genB; rw [← hn, ← hpad, ← hF, hNv, hpad]
  rw [hG]
  unfold genT
  rw [← hF] at h4 h6
  rw [← hn] at h7
  generalize F * (27 * N + 21) = A at h6 ⊢
  generalize n * (54 * N + 43) = B at h7 ⊢
  generalize powB (n + 2) E = C at h1 ⊢
  omega

end ZP.Cx
