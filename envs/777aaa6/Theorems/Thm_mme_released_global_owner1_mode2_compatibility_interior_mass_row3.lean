-- Prove2me | Theorems.Thm_mme_released_global_owner1_mode2_compatibility_interior_mass_row3
-- name    : mme_released_global_owner1_mode2_compatibility_interior_mass_row3
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T01:10:51.015986+00:00
-- url     : https://prove2.me/theorems/ff56ad3d-52c1-46ad-b071-245d9a3dbf4f
-- title:
--   owner1 mode2 compatibility interior mass row3
-- statement:
--   For owner 1, mode 2, and coordinate pool 3, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner1_mode2_compatibility_interior_mass_row3 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 2209018517550345181486299189577759500000000000000000000000, 0, 2209018517550345181486299189577759500000000000000000000000, 0, 0, 0, 2610072187628639234666810738856541251047975968000000000000, 0, 78505378738066485108814740302361001497904048064000000000000, 0, 2610072187628639234666810738856541251047975968000000000000, 0, 0, 0, 2610072456622633639415542281068566392094468845000000000000, 0, 2610072456622633639415542281068566392094468845000000000000, 0, 0, 0, 0, 0, 0, 0, 2610072187628639234666810738856541251047975968000000000000, 0, 78505378738066485108814740302361001497904048064000000000000, 0, 2610072187628639234666810738856541251047975968000000000000, 0, 0, 0, 78505352441555166113618739025128430715811062310000000000000, 0, 78505352441555166113618739025128430715811062310000000000000, 0, 0, 0, 0, 0, 2209053175825457847915515443082593000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2610072456622633639415542281068566392094468845000000000000, 0, 2610072456622633639415542281068566392094468845000000000000, 0, 0, 0, 0, 0, 2209053175825457847915515443082593000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 0).val = 0 ∨ ((shape s).val 1).val = 0) ∧ (shape s).val 2 = 3 then ((alpha 1 s * ((jointRows 1 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
