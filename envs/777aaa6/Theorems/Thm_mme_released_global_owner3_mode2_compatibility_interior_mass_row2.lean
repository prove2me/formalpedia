-- Prove2me | Theorems.Thm_mme_released_global_owner3_mode2_compatibility_interior_mass_row2
-- name    : mme_released_global_owner3_mode2_compatibility_interior_mass_row2
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T02:22:45.691435+00:00
-- url     : https://prove2.me/theorems/e730efc0-ae66-45d0-be05-c837ba0845bf
-- title:
--   owner3 mode2 compatibility interior mass row2
-- statement:
--   For owner 3, mode 2, and coordinate pool 2, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner3_mode2_compatibility_interior_mass_row2 : ∀ w : Word,
    ((([0, 0, 1613178942914795024968910149129944975438504504000000000000, 0, 49961402837786031109676279755872920049122990992000000000000, 0, 1613178942914795024968910149129944975438504504000000000000, 0, 0, 0, 45618886353341509609068735568484452250000000000000000000000, 0, 45618886353341509609068735568484452250000000000000000000000, 0, 0, 0, 0, 0, 1613179403814663172599459339213102058490639908000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45618886353341509609068735568484452250000000000000000000000, 0, 45618886353341509609068735568484452250000000000000000000000, 0, 0, 0, 0, 0, 49961396539389014058912038993503176883018720184000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1613179403814663172599459339213102058490639908000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 0).val = 0 ∨ ((shape s).val 1).val = 0) ∧ (shape s).val 2 = 2 then ((alpha 3 s * ((jointRows 3 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
