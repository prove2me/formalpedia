-- Prove2me | Theorems.Thm_mme_released_global_owner0_mode1_compatibility_interior_mass_row1
-- name    : mme_released_global_owner0_mode1_compatibility_interior_mass_row1
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T00:20:55.21046+00:00
-- url     : https://prove2.me/theorems/5ec41c03-4f2d-4647-bfcd-3653eaffdc30
-- title:
--   owner0 mode1 compatibility interior mass row1
-- statement:
--   Fix owner 0, mode 1, and coordinate pool 1. Let $N_{1,w}$ be the stated table entry, $D=10^{12}$, $\alpha_s$ the outer cell weight, and $c_{s,a}$ the integer atom multiplicity. For every four-letter word $w$,
--
--   $$\frac{N_{1,w}}{D^5}=\sum_{s:\,\operatorname{shape}(s)_{1}=1,\ \operatorname{shape}(s)_{2}\ne0}\frac{\alpha_s}{D^5}\sum_{a:\,a_{1}=w}c_{s,a}.$$
--
--   This identifies the rational table with the actual released masses used by the compatibility entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner0_mode1_compatibility_interior_mass_row1 : ∀ w : Word,
    ((([0, 28464765278801724350068313933866104000000000000000000000000, 0, 28464765278801724350068313933866104000000000000000000000000, 0, 0, 0, 0, 0, 28464765190698275649931686066133896000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28464765190698275649931686066133896000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ ((shape s).val 2).val = 0 ∧ (shape s).val 1 = 1 then ((alpha 0 s * ((jointRows 0 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
