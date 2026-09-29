-- Prove2me | Theorems.Thm_mme_released_global_owner1_mode2_compatibility_interior_mass_row1
-- name    : mme_released_global_owner1_mode2_compatibility_interior_mass_row1
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T01:10:41.266982+00:00
-- url     : https://prove2.me/theorems/93bb2af5-b34f-45f9-97c7-957f9ee61667
-- title:
--   owner1 mode2 compatibility interior mass row1
-- statement:
--   For owner 1, mode 2, and coordinate pool 1, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner1_mode2_compatibility_interior_mass_row1 : ∀ w : Word,
    ((([0, 28398352973895064975841251440889371500000000000000000000000, 0, 28398352973895064975841251440889371500000000000000000000000, 0, 0, 0, 0, 0, 28398344280604935024158748559110628500000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28398344280604935024158748559110628500000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 0).val = 0 ∨ ((shape s).val 1).val = 0) ∧ (shape s).val 2 = 1 then ((alpha 1 s * ((jointRows 1 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
