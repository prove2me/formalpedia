-- Prove2me | Theorems.Thm_mme_released_global_owner5_mode1_word_mass_row6
-- name    : mme_released_global_owner5_mode1_word_mass_row6
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T03:23:26.970916+00:00
-- url     : https://prove2.me/theorems/92086c38-efdc-426b-ae4d-17046522d1dc
-- title:
--   owner5 mode1 word mass row6
-- statement:
--   For owner 5, mode 1, and coordinate pool 6, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner5_mode1_word_mass_row6 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8253068039159625167907342496710657513918768000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 234850643886167999188719310812594684972162464000000000000, 0, 0, 0, 0, 0, 289193414287274758598968722517975000000000000000000000000, 0, 289193414272740885422968722517975000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8253068095625813759907342496710657513918768000000000000, 0, 0, 0, 0, 0, 289193414197743761054968722517975000000000000000000000000, 0, 289193414317042346230968722517975000000000000000000000000, 0, 0, 0, 8257379188441264572136593499721072834482388000000000000, 0, 235059192427176610167317927122641854331035224000000000000, 0, 8257379288626935836136593499721072834482388000000000000, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 1 = 6 then ((alpha 5 s * ((jointRows 5 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
