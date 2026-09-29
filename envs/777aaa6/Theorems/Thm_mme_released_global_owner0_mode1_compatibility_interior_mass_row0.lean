-- Prove2me | Theorems.Thm_mme_released_global_owner0_mode1_compatibility_interior_mass_row0
-- name    : mme_released_global_owner0_mode1_compatibility_interior_mass_row0
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T00:20:12.430295+00:00
-- url     : https://prove2.me/theorems/f2ae07bb-a87d-4cf0-b9f8-9aa95acdd121
-- title:
--   owner0 mode1 compatibility interior mass row0
-- statement:
--   Fix owner 0, mode 1, and coordinate pool 0. Let $N_{0,w}$ be the stated table entry, $D=10^{12}$, $\alpha_s$ the outer cell weight, and $c_{s,a}$ the integer atom multiplicity. For every four-letter word $w$,
--
--   $$\frac{N_{0,w}}{D^5}=\sum_{s:\,\operatorname{shape}(s)_{1}=0,\ \operatorname{shape}(s)_{2}\ne0}\frac{\alpha_s}{D^5}\sum_{a:\,a_{1}=w}c_{s,a}.$$
--
--   This identifies the rational table with the actual released masses used by the compatibility entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner0_mode1_compatibility_interior_mass_row0 : ∀ w : Word,
    ((([23073909000000000000000000000000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ ((shape s).val 2).val = 0 ∧ (shape s).val 1 = 0 then ((alpha 0 s * ((jointRows 0 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
