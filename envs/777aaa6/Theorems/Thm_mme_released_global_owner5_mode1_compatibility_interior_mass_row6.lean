-- Prove2me | Theorems.Thm_mme_released_global_owner5_mode1_compatibility_interior_mass_row6
-- name    : mme_released_global_owner5_mode1_compatibility_interior_mass_row6
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T03:26:43.52267+00:00
-- url     : https://prove2.me/theorems/44715c25-a02f-4a26-af45-aa48c3b000c4
-- title:
--   owner5 mode1 compatibility interior mass row6
-- statement:
--   For owner 5, mode 1, and coordinate pool 6, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner5_mode1_compatibility_interior_mass_row6 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4358008776608587535907342496710657513918768000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 146264253206947415900719310812594684972162464000000000000, 0, 0, 0, 0, 0, 213066064253025784302968722517975000000000000000000000000, 0, 213066064313569324942968722517975000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4358008742584118415907342496710657513918768000000000000, 0, 0, 0, 0, 0, 213066064247521826062968722517975000000000000000000000000, 0, 213066064321575082382968722517975000000000000000000000000, 0, 0, 0, 4363803895610484260136593499721072834482388000000000000, 0, 146530836228861969695317927122641854331035224000000000000, 0, 4363804013695406500136593499721072834482388000000000000, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 2).val = 0) ∧ (shape s).val 1 = 6 then ((alpha 5 s * ((jointRows 5 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
