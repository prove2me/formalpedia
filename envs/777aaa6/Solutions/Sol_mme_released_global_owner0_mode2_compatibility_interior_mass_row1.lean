-- Prove2me | solution 1 for mme_released_global_owner0_mode2_compatibility_interior_mass_row1
-- status  : ACCEPTED   (disprove)
-- author  : @evgeth
-- created : 2026-09-28T19:50:16.251013+00:00
-- url     : https://prove2.me/submissions/97e1d155-2c2f-47a1-af29-6867ce95694e

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem solution : ¬ (∀ w : Word,
    ((([0, 28398126275245566910706541358579060500000000000000000000000, 0, 28398126275245566910706541358579060500000000000000000000000, 0, 0, 0, 0, 0, 28398001395754433089293458641420939500000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28398001395754433089293458641420939500000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ ((shape s).val 1).val = 0 ∧ (shape s).val 2 = 1 then ((alpha 0 s * ((jointRows 0 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0) := by
  decide +kernel
