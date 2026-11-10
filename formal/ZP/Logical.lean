module

public import ZP.AllDefs
public import ZP.LogicalG
public import ZP.Abstract
public import ZP.Bridge
public import ZP.LTM
public import ZP.Logic
public import ZP.Zip
public import ZP.Outer
public import ZP.Pair

@[expose] public section

/-!
# Layer N3: the logical machine runs the abstract program

`zpLogic` (`native/zp2.py`, 129 states, 4 symbols) simulates the abstract program
beep for beep and never halts. Between pairs its tape reads `M_g J M_1 s` (symbols
`B = 0`, `M = 1`, `'0' = 2`, `'1' = 3`), with blanks everywhere else, and the machine
is in state `GRB` on the blank right of `s` (`lay J S`).

Everything here follows from one lemma, `pair_step` (proved in `ZP/Pair.lean` as
`pair_main`): from `lay J S` the machine reaches `lay` of `absStep (J, S)`, and visits
the beep state on the way iff `J` is wrong on `S`, and then exactly once.
-/

namespace ZP

/-- `I0` writes `M_g`, `JOV2` writes `M_1`: the pair `('', '')`. -/
theorem zconf_two : zpLogic.zconf 2 = some (lay 1 1) := rfl

/-- The pair data of `zpLogic`: `pair_main` is the one lemma. -/
def zpPairData : PairData zpLogic Correct where
  lay := lay
  k0 := 2
  h0 := zconf_two
  step := pair_main

theorem zpLogic_macroSim : Nonempty (LMacroSim zpLogic) := zpPairData.macroSim

end ZP
