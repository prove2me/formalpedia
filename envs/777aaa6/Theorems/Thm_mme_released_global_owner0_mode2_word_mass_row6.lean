-- Prove2me | Theorems.Thm_mme_released_global_owner0_mode2_word_mass_row6
-- name    : mme_released_global_owner0_mode2_word_mass_row6
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T00:19:50.841826+00:00
-- url     : https://prove2.me/theorems/7d0e50f0-c79f-40a4-aa22-af95431eb805
-- title:
--   owner0 mode2 word mass row6
-- statement:
--   Fix owner 0, mode 2, and coordinate pool 6. Let $N_{6,w}$ be the stated table entry, $D=10^{12}$, $\alpha_s$ the outer cell weight, and $c_{s,a}$ the integer atom multiplicity. For every four-letter word $w$,
--
--   $$\frac{N_{6,w}}{D^5}=\sum_{s:\,\operatorname{shape}(s)_{2}=6}\frac{\alpha_s}{D^5}\sum_{a:\,a_{2}=w}c_{s,a}.$$
--
--   This identifies the rational table with the actual released masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner0_mode2_word_mass_row6 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7898094598411036257203187701269782404254652000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 244380517185442822286036116805105435191490696000000000000, 0, 0, 0, 0, 0, 280094227165086354485710516095327750000000000000000000000, 0, 280094226845544514796710516095327750000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7898094595486080503203187701269782404254652000000000000, 0, 0, 0, 0, 0, 280094227463320495939710516095327750000000000000000000000, 0, 280094227345547888570710516095327750000000000000000000000, 0, 0, 0, 7898094593749669110728059443356416402871144000000000000, 0, 244380380681913350414259324524331167194257712000000000000, 0, 7898094525497787635728059443356416402871144000000000000, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 2 = 6 then ((alpha 0 s * ((jointRows 0 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
