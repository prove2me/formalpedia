-- Prove2me | Theorems.Thm_mme_released_global_owner0_mode1_word_mass_row4
-- name    : mme_released_global_owner0_mode1_word_mass_row4
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T23:54:41.114619+00:00
-- url     : https://prove2.me/theorems/e398e38a-958c-4baa-9278-39eac43219f7
-- title:
--   Outer word mass table identity, owner 0 mode 1 pool 4
-- statement:
--   Fix the released profile with owner 0 and coordinate mode 1. Let $D=10^{12}$ be its common denominator, $\alpha_s$ the outer weight of cell $s$, and $c_{s,a}$ the integer multiplicity of supported atom $a$. For every four-letter word $w$, the certified table entry $N_{4,w}$ satisfies
--
--   $$\frac{N_{4,w}}{D^5}=\sum_{s:\,\operatorname{shape}(s)_1=4}\frac{\alpha_s}{D^5}\sum_{a:\,a_1=w}c_{s,a}.$$
--
--   This identifies coordinate pool 4 of the rational entropy table with the actual released word masses. The table entries are fixed explicitly in the formal statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner0_mode1_word_mass_row4 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 96395223203745806974078936355179000000000000000000000000, 0, 0, 0, 0, 0, 3939817973019890966421413808762346000000000000000000000000, 0, 3939817973246493092149413808762346000000000000000000000000, 0, 0, 0, 97271216812545468569698773622099652138814519632247077268, 0, 4079465000467900233534037374002077840327276791735505845464, 0, 97271216737823872153698773622099652138814519632247077268, 0, 0, 0, 0, 0, 0, 0, 3939817973082321452533413808762346000000000000000000000000, 0, 3939817973107391140437413808762346000000000000000000000000, 0, 0, 0, 4079464882986368637162541344719752832959566152735505845464, 0, 141663070469515003372773612484563479044871056032528988309072, 0, 4079464879200219196234541344719752832959566152735505845464, 0, 0, 0, 3939817599308379140764234324509892750000000000000000000000, 0, 3939817598869415868796234324509892750000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 97271216812545468569698773622099652138814519632247077268, 0, 4079465005425048079966037374002077840327276791735505845464, 0, 97271216812545468569698773622099652138814519632247077268, 0, 0, 0, 3939817599179130962876234324509892750000000000000000000000, 0, 3939817599209562791036234324509892750000000000000000000000, 0, 0, 0, 0, 0, 96394189003668980477763514060327000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD
      (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) /
      1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 1 = 4 then
      ((alpha 0 s * ((jointRows 0 s).map
        (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) /
          (denominator : ℚ) ^ 5 else 0 := by sorry
