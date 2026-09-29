-- Prove2me | Theorems.Thm_mme_released_global_owner2_mode1_compatibility_interior_mass_row2
-- name    : mme_released_global_owner2_mode1_compatibility_interior_mass_row2
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T01:42:30.163987+00:00
-- url     : https://prove2.me/theorems/25040d75-074a-4a8e-9062-a49f342ffdb5
-- title:
--   owner2 mode1 compatibility interior mass row2
-- statement:
--   For owner 2, mode 1, and coordinate pool 2, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner2_mode1_compatibility_interior_mass_row2 : ∀ w : Word,
    ((([0, 0, 1730317787534958172191392392217492144816613826000000000000, 0, 49751550475982390442293130583953653710366772348000000000000, 0, 1730317787598177778335392392217492144816613826000000000000, 0, 0, 0, 45667849438276326138869504611130576750000000000000000000000, 0, 45667849438357820162414504611130576750000000000000000000000, 0, 0, 0, 0, 0, 1730318150806595235030162255277463680638607365000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45667849437909356081330504611130576750000000000000000000000, 0, 45667849437876264568739504611130576750000000000000000000000, 0, 0, 0, 0, 0, 49751549006851516185765741676534127638722785270000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1730318150806595235030162255277463680638607365000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 2).val = 0) ∧ (shape s).val 1 = 2 then ((alpha 2 s * ((jointRows 2 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
