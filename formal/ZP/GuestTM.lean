module

public import ZP.Rot
public import ZP.Complexity

@[expose] public section

/-!
# A guest code is a Turing machine

Every code a guest run reaches is a rotation `rotl j R0` of its start code `R0`
with `j < |R0|` (`rot_rotl`). So the offsets `j` are the states of a machine
`gMach R0` of the model in `ZP/Complexity.lean`, and that machine runs exactly
like the guest, step for step (`sim`, `run_eq`).
-/

namespace ZP.Cx

variable (R0 : List Bool)

/-- The offset after one `rot`. -/
def nxt (q : Nat) : Nat := (entryOnes (rotl q R0) + 3 + q) % R0.length

def nxtN : Nat → Nat → Nat
  | 0, q => q
  | n + 1, q => nxtN n (nxt R0 q)

/-- The action of state `q` on symbol `s`. -/
def gAct (q : Nat) (s : Option Bool) : Act :=
  if (rotl (nxtN R0 (iota s) q) R0).getD 2 false then
    .go ((rotl (nxtN R0 (iota s) q) R0).getD 0 false)
      ((rotl (nxtN R0 (iota s) q) R0).getD 1 false)
      (nxtN R0 (entryOnes (rotl (nxtN R0 (iota s) q) R0) + 2) (nxtN R0 (iota s) q))
  else .halt ((rotl (nxtN R0 (iota s) q) R0).getD 0 false)

def gMach : Mach :=
  ⟨(List.range R0.length).map fun q => (gAct R0 q none, gAct R0 q (some false),
    gAct R0 q (some true))⟩

theorem rotl_mod' (K : Nat) : rotl K R0 = rotl (K % R0.length) R0 := by
  rw [rotl_mod, rotl_mod (K % R0.length), Nat.mod_mod]

theorem rot_rotl (q : Nat) : rot (rotl q R0) = rotl (nxt R0 q) R0 := by
  rw [rot_eq, ← rotl_add, rotl_mod' R0 (entryOnes (rotl q R0) + 3 + q)]
  rfl

theorem rotN_rotl : ∀ (n q : Nat), rotN n (rotl q R0) = rotl (nxtN R0 n q) R0
  | 0, _ => rfl
  | n + 1, q => by
    show rotN n (rot (rotl q R0)) = _
    rw [rot_rotl]
    exact rotN_rotl n (nxt R0 q)

theorem nxt_lt {q : Nat} (hq : q < R0.length) (q' : Nat) : nxt R0 q' < R0.length :=
  Nat.mod_lt _ (by omega)

theorem nxtN_lt {q : Nat} (hq : q < R0.length) : ∀ n, nxtN R0 n q < R0.length
  | 0 => hq
  | n + 1 => nxtN_lt (nxt_lt R0 hq q) n

theorem act_gMach {q : Nat} (hq : q < R0.length) (s : Option Bool) :
    (gMach R0).act q s = gAct R0 q s := by
  cases s with
  | none => simp [Mach.act, gMach, hq]
  | some b => cases b <;> simp [Mach.act, gMach, hq]

theorem exec_succ (M : Mach) (T q : Nat) (tape : Nat → Option Bool) (h : Nat) :
    exec M (T + 1) q tape h =
      (match M.act q (tape h) with
        | .halt b => some b
        | .go w r q' => exec M T q' (write tape h w) (move r h)) := rfl

theorem runAux_succ (T : Nat) (R : List Bool) (tape : Nat → Option Bool) (h : Nat) :
    runAux (T + 1) R tape h =
      (if (rotN (iota (tape h)) R).getD 2 false then
        runAux T (rotN (entryOnes (rotN (iota (tape h)) R) + 2) (rotN (iota (tape h)) R))
          (write tape h ((rotN (iota (tape h)) R).getD 0 false))
          (move ((rotN (iota (tape h)) R).getD 1 false) h)
      else (rotN (iota (tape h)) R).getD 0 false) := rfl

/-- The machine runs like the guest. -/
theorem sim : ∀ (T q : Nat) (tape : Nat → Option Bool) (h : Nat), q < R0.length →
    (exec (gMach R0) T q tape h).getD false = runAux T (rotl q R0) tape h
  | 0, _, _, _, _ => rfl
  | T + 1, q, tape, h, hq => by
    rw [exec_succ, act_gMach R0 hq, runAux_succ, rotN_rotl R0 (iota (tape h)) q, gAct]
    rw [rotN_rotl R0 (entryOnes (rotl (nxtN R0 (iota (tape h)) q) R0) + 2)]
    by_cases hc : (rotl (nxtN R0 (iota (tape h)) q) R0).getD 2 false = true
    · simp only [if_pos hc]
      exact sim T _ _ _ (nxtN_lt R0 (nxtN_lt R0 hq _) _)
    · simp only [if_neg hc]
      try rfl

theorem length_rot (R : List Bool) : (rot R).length = R.length := by
  unfold rot
  simp only [List.length_append, List.length_drop, List.length_take]
  have := Nat.mod_le (entryOnes R + 3) R.length
  omega

/-- The start code of program `P`. -/
def startCode (P : List Bool) : List Bool := rot (P.reverse ++ [false])

theorem startCode_pos (P : List Bool) : 0 < (startCode P).length := by
  unfold startCode
  rw [length_rot]
  simp

/-- The guest run of `P` is the run of the machine `gMach (startCode P)`. -/
theorem run_eq (P x : List Bool) (T : Nat) :
    run P x T = (exec (gMach (startCode P)) T 0 (inTape x) 0).getD false :=
  (sim (startCode P) T 0 (inTape x) 0 (startCode_pos P)).symm

end ZP.Cx
