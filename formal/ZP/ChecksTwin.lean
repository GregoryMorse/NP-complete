module

public import ZP.AllDefs

@[expose] public section

namespace ZP

theorem twin_table_length : twinMachine.table.length = 19 := by decide

theorem isPrime_small :
    (List.range 31).filter (fun p => decide (IsPrime p)) =
      [2, 3, 5, 7, 11, 13, 17, 19, 23, 29] := by decide

end ZP
