-- Prove2me | Theorems.Thm_mme_released_global_owner0_mode1_compatibility_interior_mass_row3
-- name    : mme_released_global_owner0_mode1_compatibility_interior_mass_row3
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T00:20:27.67723+00:00
-- url     : https://prove2.me/theorems/1f45b311-f07f-4feb-98c6-64414af6f912
-- title:
--   owner0 mode1 compatibility interior mass row3
-- statement:
--   Fix owner 0, mode 1, and coordinate pool 3. Let $N_{3,w}$ be the stated table entry, $D=10^{12}$, $\alpha_s$ the outer cell weight, and $c_{s,a}$ the integer atom multiplicity. For every four-letter word $w$,
--
--   $$\frac{N_{3,w}}{D^5}=\sum_{s:\,\operatorname{shape}(s)_{1}=3,\ \operatorname{shape}(s)_{2}\ne0}\frac{\alpha_s}{D^5}\sum_{a:\,a_{1}=w}c_{s,a}.$$
--
--   This identifies the rational table with the actual released masses used by the compatibility entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner0_mode1_compatibility_interior_mass_row3 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 2261543719755050192771247006846223000000000000000000000000, 0, 2261543719726431684863247006846223000000000000000000000000, 0, 0, 0, 2697007013908082558720879189857629091240013050500000000000, 0, 79351929113459040439997159993598014317519973899000000000000, 0, 2697007013826996786314879189857629091240013050500000000000, 0, 0, 0, 2697007073182889885750510703584531351692896695500000000000, 0, 2697007073178120134432510703584531351692896695500000000000, 0, 0, 0, 0, 0, 0, 0, 2697007013831766537632879189857629091240013050500000000000, 0, 79351929116754938600735159993598014317519973899000000000000, 0, 2697007013836536288950879189857629091240013050500000000000, 0, 0, 0, 79351900284200921334514177163082770796614206609000000000000, 0, 79351900275419809158076177163082770796614206609000000000000, 0, 0, 0, 0, 0, 2261575615279203188528636049588671000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2697007073182889885750510703584531351692896695500000000000, 0, 2697007073178120134432510703584531351692896695500000000000, 0, 0, 0, 0, 0, 2261575615279203188528636049588671000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ ((shape s).val 2).val = 0 ∧ (shape s).val 1 = 3 then ((alpha 0 s * ((jointRows 0 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
