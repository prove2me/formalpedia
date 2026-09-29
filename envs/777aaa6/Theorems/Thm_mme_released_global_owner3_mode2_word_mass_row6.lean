-- Prove2me | Theorems.Thm_mme_released_global_owner3_mode2_word_mass_row6
-- name    : mme_released_global_owner3_mode2_word_mass_row6
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T02:18:11.114964+00:00
-- url     : https://prove2.me/theorems/cf9d62bb-e9b4-4134-9dfa-3635b03d3b99
-- title:
--   owner3 mode2 word mass row6
-- statement:
--   For owner 3, mode 2, and coordinate pool 6, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner3_mode2_word_mass_row6 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7897526347242040441083235851218098064936904000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 244394959445738955843245866188939803870126192000000000000, 0, 0, 0, 0, 0, 280095901145195644209957940572859500000000000000000000000, 0, 280095901302628923537957940572859500000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7897526732511877449083235851218098064936904000000000000, 0, 0, 0, 0, 0, 280095901063870075649957940572859500000000000000000000000, 0, 280095901468859340217957940572859500000000000000000000000, 0, 0, 0, 7897526818554971186303567638115325096485394000000000000, 0, 244415718853430319814148764540955349807029212000000000000, 0, 7897526821967851650303567638115325096485394000000000000, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 2 = 6 then ((alpha 3 s * ((jointRows 3 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
