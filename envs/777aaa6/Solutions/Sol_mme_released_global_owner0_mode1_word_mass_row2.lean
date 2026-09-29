-- Prove2me | solution 1 for mme_released_global_owner0_mode1_word_mass_row2
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T00:00:07.591546+00:00
-- url     : https://prove2.me/submissions/b3e3b1e2-96f2-4239-9b51-b62127731742

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

/-- The exact released global word masses in coordinate pool 2 agree with the corresponding rational table row. This certifies the table identity used in the outer word entropy bound. -/
theorem solution : ∀ w : Word,
    ((([0, 0, 1731632834340990212368375801271512207146759350000000000000, 0, 49832805501607662044340492489679709585706481300000000000000, 0, 1731632834381721756710375801271512207146759350000000000000, 0, 0, 0, 45751443989419924136288423703666371500000000000000000000000, 0, 45751443989814562990925423703666371500000000000000000000000, 0, 0, 0, 0, 0, 1731632637117159997518472948883415228611635041000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45751443989313606652004423703666371500000000000000000000000, 0, 45751443989734724473483423703666371500000000000000000000000, 0, 0, 0, 0, 0, 49832807441271645581241115195344949542776729918000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1731632636998002155119472948883415228611635041000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD
      (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) /
      1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 1 = 2 then
      ((alpha 0 s * ((jointRows 0 s).map
        (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) /
          (denominator : ℚ) ^ 5 else 0 := by
  decide +kernel

#print axioms solution
