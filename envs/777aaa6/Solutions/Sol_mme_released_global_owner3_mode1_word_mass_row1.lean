-- Prove2me | solution 1 for mme_released_global_owner3_mode1_word_mass_row1
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T02:16:32.196458+00:00
-- url     : https://prove2.me/submissions/96c1c75b-3a7b-4d19-94b6-2e6a73dd621b

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

/-- The released rational table agrees with the joint atom masses. -/
theorem solution : ∀ w : Word,
    ((([0, 28468966199693409882099528520550393500000000000000000000000, 0, 28468966199693409882099528520550393500000000000000000000000, 0, 0, 0, 0, 0, 28468947850306590117900471479449606500000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28468947850306590117900471479449606500000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 1 = 1 then ((alpha 3 s * ((jointRows 3 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by
  decide +kernel

#print axioms solution
