-- Prove2me | solution 1 for mme_released_global_owner0_mode1_word_mass_row0
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T23:57:03.25521+00:00
-- url     : https://prove2.me/submissions/9edc0f0a-54e4-4754-8a3d-b53c153909a2

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

/-- The exact released global word masses in coordinate pool 0 agree with the corresponding rational table row. This certifies the table identity used in the outer word entropy bound. -/
theorem solution : ∀ w : Word,
    ((([23074029039000000000000000000000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD
      (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) /
      1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 1 = 0 then
      ((alpha 0 s * ((jointRows 0 s).map
        (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) /
          (denominator : ℚ) ^ 5 else 0 := by
  decide +kernel

#print axioms solution
