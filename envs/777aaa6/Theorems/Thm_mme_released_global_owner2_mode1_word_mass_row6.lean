-- Prove2me | Theorems.Thm_mme_released_global_owner2_mode1_word_mass_row6
-- name    : mme_released_global_owner2_mode1_word_mass_row6
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T01:39:04.136854+00:00
-- url     : https://prove2.me/theorems/c47fe326-a7b2-4275-ad31-af68df4a5c7a
-- title:
--   owner2 mode1 word mass row6
-- statement:
--   For owner 2, mode 1, and coordinate pool 6, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner2_mode1_word_mass_row6 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8253729197236031829887342102772828442113000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 234852468282239812640075403646198343115774000000000000000, 0, 0, 0, 0, 0, 289266711128850206762817409209807000000000000000000000000, 0, 289266710767349290455817409209807000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8253729227970498269887342102772828442113000000000000000, 0, 0, 0, 0, 0, 289266710776364300238817409209807000000000000000000000000, 0, 289266710788481410338817409209807000000000000000000000000, 0, 0, 0, 8253728539744087062043926061430965707331004000000000000, 0, 234852443749521668807792423186166068585337992000000000000, 0, 8253728542242693594043926061430965707331004000000000000, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 1 = 6 then ((alpha 2 s * ((jointRows 2 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
