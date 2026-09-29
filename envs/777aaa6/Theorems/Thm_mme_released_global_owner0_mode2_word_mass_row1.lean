-- Prove2me | Theorems.Thm_mme_released_global_owner0_mode2_word_mass_row1
-- name    : mme_released_global_owner0_mode2_word_mass_row1
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T00:20:37.988401+00:00
-- url     : https://prove2.me/theorems/1213e82e-3acd-49bc-bb52-399253f27ef8
-- title:
--   owner0 mode2 word mass row1
-- statement:
--   Fix owner 0, mode 2, and coordinate pool 1. Let $N_{1,w}$ be the stated table entry, $D=10^{12}$, $\alpha_s$ the outer cell weight, and $c_{s,a}$ the integer atom multiplicity. For every four-letter word $w$,
--
--   $$\frac{N_{1,w}}{D^5}=\sum_{s:\,\operatorname{shape}(s)_{2}=1}\frac{\alpha_s}{D^5}\sum_{a:\,a_{2}=w}c_{s,a}.$$
--
--   This identifies the rational table with the actual released masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner0_mode2_word_mass_row1 : ∀ w : Word,
    ((([0, 28406481686745566910706541358579060500000000000000000000000, 0, 28406481686745566910706541358579060500000000000000000000000, 0, 0, 0, 0, 0, 28406356807254433089293458641420939500000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28406356807254433089293458641420939500000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 2 = 1 then ((alpha 0 s * ((jointRows 0 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
