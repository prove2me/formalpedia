-- Prove2me | Theorems.Thm_mme_released_global_owner4_mode2_compatibility_interior_mass_row5
-- name    : mme_released_global_owner4_mode2_compatibility_interior_mass_row5
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T02:57:38.08919+00:00
-- url     : https://prove2.me/theorems/fa4b2851-ab9f-447d-becd-e0ebff5b6c35
-- title:
--   owner4 mode2 compatibility interior mass row5
-- statement:
--   For owner 4, mode 2, and coordinate pool 5, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner4_mode2_compatibility_interior_mass_row5 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 63880734154989965207506682869438000000000000000000000000, 0, 0, 0, 0, 0, 79224007483767642300418664962579954440418430000000000000, 0, 79224007483767642300418664962579954440418430000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 63880734154989965207506682869438000000000000000000000000, 0, 0, 0, 0, 0, 4608717878169769448745979912440130091119163140000000000000, 0, 4608717878169769448745979912440130091119163140000000000000, 0, 0, 0, 79224018008189368507107027119593087835175758000000000000, 0, 4608718547207684920313929484702113824329648484000000000000, 0, 79224018008189368507107027119593087835175758000000000000, 0, 0, 0, 0, 0, 0, 0, 79224007483767642300418664962579954440418430000000000000, 0, 79224007483767642300418664962579954440418430000000000000, 0, 0, 0, 79224018008189368507107027119593087835175758000000000000, 0, 4608718547207684920313929484702113824329648484000000000000, 0, 79224018008189368507107027119593087835175758000000000000, 0, 0, 0, 63880332483641644117532535823972000000000000000000000000, 0, 63880332483641644117532535823972000000000000000000000000, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 0).val = 0 ∨ ((shape s).val 1).val = 0) ∧ (shape s).val 2 = 5 then ((alpha 4 s * ((jointRows 4 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
