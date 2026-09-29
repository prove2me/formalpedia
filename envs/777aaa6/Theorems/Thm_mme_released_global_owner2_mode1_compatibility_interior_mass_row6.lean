-- Prove2me | Theorems.Thm_mme_released_global_owner2_mode1_compatibility_interior_mass_row6
-- name    : mme_released_global_owner2_mode1_compatibility_interior_mass_row6
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T01:43:09.320454+00:00
-- url     : https://prove2.me/theorems/5f2b9344-02bd-418d-b073-64be093e986c
-- title:
--   owner2 mode1 compatibility interior mass row6
-- statement:
--   For owner 2, mode 1, and coordinate pool 6, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner2_mode1_compatibility_interior_mass_row6 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4358116006365695909887342102772828442113000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 146250275341363765640075403646198343115774000000000000000, 0, 0, 0, 0, 0, 213139952700513006202817409209807000000000000000000000000, 0, 213139952295747522335817409209807000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4358115826247557229887342102772828442113000000000000000, 0, 0, 0, 0, 0, 213139952306254413758817409209807000000000000000000000000, 0, 213139952336274103538817409209807000000000000000000000000, 0, 0, 0, 4358114900314671382043926061430965707331004000000000000, 0, 146250244384603279967792423186166068585337992000000000000, 0, 4358114902315984034043926061430965707331004000000000000, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 2).val = 0) ∧ (shape s).val 1 = 6 then ((alpha 2 s * ((jointRows 2 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
