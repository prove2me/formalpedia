-- Prove2me | Theorems.Thm_mme_released_global_owner0_mode2_word_mass_row5
-- name    : mme_released_global_owner0_mode2_word_mass_row5
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T00:20:55.158846+00:00
-- url     : https://prove2.me/theorems/cc2ba729-25b0-4895-897c-3840926f80e3
-- title:
--   owner0 mode2 word mass row5
-- statement:
--   Fix owner 0, mode 2, and coordinate pool 5. Let $N_{5,w}$ be the stated table entry, $D=10^{12}$, $\alpha_s$ the outer cell weight, and $c_{s,a}$ the integer atom multiplicity. For every four-letter word $w$,
--
--   $$\frac{N_{5,w}}{D^5}=\sum_{s:\,\operatorname{shape}(s)_{2}=5}\frac{\alpha_s}{D^5}\sum_{a:\,a_{2}=w}c_{s,a}.$$
--
--   This identifies the rational table with the actual released masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner0_mode2_word_mass_row5 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 174660422998789679956422216097224000000000000000000000000, 0, 0, 0, 0, 0, 185555180370518590941622069329054399254666133000000000000, 0, 185555180375288342259622069329054399254666133000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 174660422998789679956422216097224000000000000000000000000, 0, 0, 0, 0, 0, 6657614654060241432897943750237065201490667734000000000000, 0, 6657614654670982541373943750237065201490667734000000000000, 0, 0, 0, 185555163851235973057270075265793892321203606000000000000, 0, 6657613481020289868789423475056003215357592788000000000000, 0, 185555163860626310245270075265793892321203606000000000000, 0, 0, 0, 0, 0, 0, 0, 185555180370518590941622069329054399254666133000000000000, 0, 185555180370568312757622069329054399254666133000000000000, 0, 0, 0, 185555163860576588429270075265793892321203606000000000000, 0, 6657613482477461416565423475056003215357592788000000000000, 0, 185555163936942331333270075265793892321203606000000000000, 0, 0, 0, 174661034867195872040426269420011000000000000000000000000, 0, 174661034909974468454426269420011000000000000000000000000, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 2 = 5 then ((alpha 0 s * ((jointRows 0 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
