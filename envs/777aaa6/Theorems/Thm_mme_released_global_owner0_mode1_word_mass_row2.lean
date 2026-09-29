-- Prove2me | Theorems.Thm_mme_released_global_owner0_mode1_word_mass_row2
-- name    : mme_released_global_owner0_mode1_word_mass_row2
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T23:54:29.997544+00:00
-- url     : https://prove2.me/theorems/002fc298-d354-4707-bde3-d30b6b1ce70d
-- title:
--   Outer word mass table identity, owner 0 mode 1 pool 2
-- statement:
--   Fix the released profile with owner 0 and coordinate mode 1. Let $D=10^{12}$ be its common denominator, $\alpha_s$ the outer weight of cell $s$, and $c_{s,a}$ the integer multiplicity of supported atom $a$. For every four-letter word $w$, the certified table entry $N_{2,w}$ satisfies
--
--   $$\frac{N_{2,w}}{D^5}=\sum_{s:\,\operatorname{shape}(s)_1=2}\frac{\alpha_s}{D^5}\sum_{a:\,a_1=w}c_{s,a}.$$
--
--   This identifies coordinate pool 2 of the rational entropy table with the actual released word masses. The table entries are fixed explicitly in the formal statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner0_mode1_word_mass_row2 : ∀ w : Word,
    ((([0, 0, 1731632834340990212368375801271512207146759350000000000000, 0, 49832805501607662044340492489679709585706481300000000000000, 0, 1731632834381721756710375801271512207146759350000000000000, 0, 0, 0, 45751443989419924136288423703666371500000000000000000000000, 0, 45751443989814562990925423703666371500000000000000000000000, 0, 0, 0, 0, 0, 1731632637117159997518472948883415228611635041000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45751443989313606652004423703666371500000000000000000000000, 0, 45751443989734724473483423703666371500000000000000000000000, 0, 0, 0, 0, 0, 49832807441271645581241115195344949542776729918000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1731632636998002155119472948883415228611635041000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD
      (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) /
      1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 1 = 2 then
      ((alpha 0 s * ((jointRows 0 s).map
        (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) /
          (denominator : ℚ) ^ 5 else 0 := by sorry
