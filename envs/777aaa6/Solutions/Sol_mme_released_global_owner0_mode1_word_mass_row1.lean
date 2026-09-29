-- Prove2me | solution 1 for mme_released_global_owner0_mode1_word_mass_row1
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T23:57:04.112533+00:00
-- url     : https://prove2.me/submissions/744b86c8-6bd6-4e91-b25e-ae430ec6536c

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

/-- The exact released global word masses in coordinate pool 1 agree with the corresponding rational table row. This certifies the table identity used in the outer word entropy bound. -/
theorem solution : ∀ w : Word,
    ((([0, 28468916298051724350068313933866104000000000000000000000000, 0, 28468916298051724350068313933866104000000000000000000000000, 0, 0, 0, 0, 0, 28468916209948275649931686066133896000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28468916209948275649931686066133896000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD
      (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) /
      1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 1 = 1 then
      ((alpha 0 s * ((jointRows 0 s).map
        (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) /
          (denominator : ℚ) ^ 5 else 0 := by
  decide +kernel

#print axioms solution
