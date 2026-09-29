-- Prove2me | Theorems.Thm_mme_released_global_owner0_mode1_compatibility_interior_mass_row6
-- name    : mme_released_global_owner0_mode1_compatibility_interior_mass_row6
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T00:20:57.233823+00:00
-- url     : https://prove2.me/theorems/10206b99-1137-49c5-9ef1-6b8da46d8cd7
-- title:
--   owner0 mode1 compatibility interior mass row6
-- statement:
--   Fix owner 0, mode 1, and coordinate pool 6. Let $N_{6,w}$ be the stated table entry, $D=10^{12}$, $\alpha_s$ the outer cell weight, and $c_{s,a}$ the integer atom multiplicity. For every four-letter word $w$,
--
--   $$\frac{N_{6,w}}{D^5}=\sum_{s:\,\operatorname{shape}(s)_{1}=6,\ \operatorname{shape}(s)_{2}\ne0}\frac{\alpha_s}{D^5}\sum_{a:\,a_{1}=w}c_{s,a}.$$
--
--   This identifies the rational table with the actual released masses used by the compatibility entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner0_mode1_compatibility_interior_mass_row6 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4332892174577221283621661424410707841378990000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 146300343983338827237546072900290584317242020000000000000, 0, 0, 0, 0, 0, 213092046778830446386852851768514000000000000000000000000, 0, 213092046768323086873852851768514000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4332892067502224341621661424410707841378990000000000000, 0, 0, 0, 0, 0, 213092046775828343668852851768514000000000000000000000000, 0, 213092046736801008334852851768514000000000000000000000000, 0, 0, 0, 4338769958610247309860225292823362354565060000000000000, 0, 146571675760052063278078746591185275290869880000000000000, 0, 4338769996136531284860225292823362354565060000000000000, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ ((shape s).val 2).val = 0 ∧ (shape s).val 1 = 6 then ((alpha 0 s * ((jointRows 0 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
