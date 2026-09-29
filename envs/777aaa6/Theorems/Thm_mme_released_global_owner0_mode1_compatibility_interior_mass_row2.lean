-- Prove2me | Theorems.Thm_mme_released_global_owner0_mode1_compatibility_interior_mass_row2
-- name    : mme_released_global_owner0_mode1_compatibility_interior_mass_row2
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T00:21:01.179439+00:00
-- url     : https://prove2.me/theorems/518fc2c4-b422-4e3c-8e53-b374617fd6ee
-- title:
--   owner0 mode1 compatibility interior mass row2
-- statement:
--   Fix owner 0, mode 1, and coordinate pool 2. Let $N_{2,w}$ be the stated table entry, $D=10^{12}$, $\alpha_s$ the outer cell weight, and $c_{s,a}$ the integer atom multiplicity. For every four-letter word $w$,
--
--   $$\frac{N_{2,w}}{D^5}=\sum_{s:\,\operatorname{shape}(s)_{1}=2,\ \operatorname{shape}(s)_{2}\ne0}\frac{\alpha_s}{D^5}\sum_{a:\,a_{1}=w}c_{s,a}.$$
--
--   This identifies the rational table with the actual released masses used by the compatibility entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner0_mode1_compatibility_interior_mass_row2 : ∀ w : Word,
    ((([0, 0, 1728168539978516677423375801271512207146759350000000000000, 0, 49754659268374776161355492489679709585706481300000000000000, 0, 1728168540006174085495375801271512207146759350000000000000, 0, 0, 0, 45668268551250330882188423703666371500000000000000000000000, 0, 45668268551643461182640423703666371500000000000000000000000, 0, 0, 0, 0, 0, 1728168342465044059053472948883415228611635041000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45668268551234526649004423703666371500000000000000000000000, 0, 45668268551554068488693423703666371500000000000000000000000, 0, 0, 0, 0, 0, 49754661210029045519666115195344949542776729918000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1728168342464056294479472948883415228611635041000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ ((shape s).val 2).val = 0 ∧ (shape s).val 1 = 2 then ((alpha 0 s * ((jointRows 0 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
