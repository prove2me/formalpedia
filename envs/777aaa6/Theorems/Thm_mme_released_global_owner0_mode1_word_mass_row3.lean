-- Prove2me | Theorems.Thm_mme_released_global_owner0_mode1_word_mass_row3
-- name    : mme_released_global_owner0_mode1_word_mass_row3
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T23:54:30.948296+00:00
-- url     : https://prove2.me/theorems/594d906a-249f-4314-b2a1-8e741601691e
-- title:
--   Outer word mass table identity, owner 0 mode 1 pool 3
-- statement:
--   Fix the released profile with owner 0 and coordinate mode 1. Let $D=10^{12}$ be its common denominator, $\alpha_s$ the outer weight of cell $s$, and $c_{s,a}$ the integer multiplicity of supported atom $a$. For every four-letter word $w$, the certified table entry $N_{3,w}$ satisfies
--
--   $$\frac{N_{3,w}}{D^5}=\sum_{s:\,\operatorname{shape}(s)_1=3}\frac{\alpha_s}{D^5}\sum_{a:\,a_1=w}c_{s,a}.$$
--
--   This identifies coordinate pool 3 of the rational entropy table with the actual released word masses. The table entries are fixed explicitly in the formal statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner0_mode1_word_mass_row3 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 2314239795355160120903247006846223000000000000000000000000, 0, 2314239795326541612995247006846223000000000000000000000000, 0, 0, 0, 2743552613733777529010879189857629091240013050500000000000, 0, 80388359405802852881675159993598014317519973899000000000000, 0, 2743552613647962886838879189857629091240013050500000000000, 0, 0, 0, 2743552672275610042310510703584531351692896695500000000000, 0, 2743552672270840290992510703584531351692896695500000000000, 0, 0, 0, 0, 0, 0, 0, 2743552613652732638156879189857629091240013050500000000000, 0, 80388359412669047715743159993598014317519973899000000000000, 0, 2743552613657502389474879189857629091240013050500000000000, 0, 0, 0, 80388330845447184150016177163082770796614206609000000000000, 0, 80388330836831582415388177163082770796614206609000000000000, 0, 0, 0, 0, 0, 2314271169403199671010636049588671000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2743552672275610042310510703584531351692896695500000000000, 0, 2743552672270840290992510703584531351692896695500000000000, 0, 0, 0, 0, 0, 2314271169379555322180636049588671000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD
      (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) /
      1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 1 = 3 then
      ((alpha 0 s * ((jointRows 0 s).map
        (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) /
          (denominator : ℚ) ^ 5 else 0 := by sorry
