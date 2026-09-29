-- Prove2me | Theorems.Thm_mme_released_global_owner0_mode2_word_mass_row2
-- name    : mme_released_global_owner0_mode2_word_mass_row2
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T00:20:41.848763+00:00
-- url     : https://prove2.me/theorems/ff562c7a-c651-42dc-802a-633d867a6c00
-- title:
--   owner0 mode2 word mass row2
-- statement:
--   Fix owner 0, mode 2, and coordinate pool 2. Let $N_{2,w}$ be the stated table entry, $D=10^{12}$, $\alpha_s$ the outer cell weight, and $c_{s,a}$ the integer atom multiplicity. For every four-letter word $w$,
--
--   $$\frac{N_{2,w}}{D^5}=\sum_{s:\,\operatorname{shape}(s)_{2}=2}\frac{\alpha_s}{D^5}\sum_{a:\,a_{2}=w}c_{s,a}.$$
--
--   This identifies the rational table with the actual released masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner0_mode2_word_mass_row2 : ∀ w : Word,
    ((([0, 0, 1626374391478715223601563593563294455663444627000000000000, 0, 50098353330511891995011645611897446088673110746000000000000, 0, 1626374391436609316743563593563294455663444627000000000000, 0, 0, 0, 45789377812625857366740310120904261500000000000000000000000, 0, 45789377812685747428541310120904261500000000000000000000000, 0, 0, 0, 0, 0, 1626373444299702909168547473710229267942254307000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45789377812734215340316310120904261500000000000000000000000, 0, 45789377812668904498766310120904261500000000000000000000000, 0, 0, 0, 0, 0, 50098335043151069168012891769938460464115491386000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1626373444407286753097547473710229267942254307000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 2 = 2 then ((alpha 0 s * ((jointRows 0 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
