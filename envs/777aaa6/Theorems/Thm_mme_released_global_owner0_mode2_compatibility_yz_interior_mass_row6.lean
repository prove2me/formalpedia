-- Prove2me | Theorems.Thm_mme_released_global_owner0_mode2_compatibility_yz_interior_mass_row6
-- name    : mme_released_global_owner0_mode2_compatibility_yz_interior_mass_row6
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T00:34:25.635191+00:00
-- url     : https://prove2.me/theorems/c8f01266-1227-4f06-aebe-56d282e699b2
-- title:
--   owner0 mode2 compatibility interior mass row6
-- statement:
--   Exact released mode-2 compatibility mass identity. The boundary consists of cells with coordinate 0 equal to zero or coordinate 1 equal to zero; interior rows exclude both boundary cases. The integer table and rational atom sum are equal for every word.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner0_mode2_compatibility_yz_interior_mass_row6 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 259812754739137203187701269782404254652000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 75230625684489640344036116805105435191490696000000000000, 0, 0, 0, 0, 0, 126823942793188451024710516095327750000000000000000000000, 0, 126823942793188451024710516095327750000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 259812754739137203187701269782404254652000000000000, 0, 0, 0, 0, 0, 126823942793188451024710516095327750000000000000000000000, 0, 126823942793188451024710516095327750000000000000000000000, 0, 0, 0, 259812001300072728059443356416402871144000000000000, 0, 75230420893244477137259324524331167194257712000000000000, 0, 259812001300072728059443356416402871144000000000000, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 0).val = 0 ∨ ((shape s).val 1).val = 0) ∧ (shape s).val 2 = 6 then ((alpha 0 s * ((jointRows 0 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
