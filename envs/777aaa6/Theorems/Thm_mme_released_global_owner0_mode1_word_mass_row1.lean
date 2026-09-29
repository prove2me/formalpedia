-- Prove2me | Theorems.Thm_mme_released_global_owner0_mode1_word_mass_row1
-- name    : mme_released_global_owner0_mode1_word_mass_row1
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T23:54:37.158905+00:00
-- url     : https://prove2.me/theorems/a0570e16-1c86-46a1-a70b-afec5fdfdf40
-- title:
--   Outer word mass table identity, owner 0 mode 1 pool 1
-- statement:
--   Fix the released profile with owner 0 and coordinate mode 1. Let $D=10^{12}$ be its common denominator, $\alpha_s$ the outer weight of cell $s$, and $c_{s,a}$ the integer multiplicity of supported atom $a$. For every four-letter word $w$, the certified table entry $N_{1,w}$ satisfies
--
--   $$\frac{N_{1,w}}{D^5}=\sum_{s:\,\operatorname{shape}(s)_1=1}\frac{\alpha_s}{D^5}\sum_{a:\,a_1=w}c_{s,a}.$$
--
--   This identifies coordinate pool 1 of the rational entropy table with the actual released word masses. The table entries are fixed explicitly in the formal statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner0_mode1_word_mass_row1 : ∀ w : Word,
    ((([0, 28468916298051724350068313933866104000000000000000000000000, 0, 28468916298051724350068313933866104000000000000000000000000, 0, 0, 0, 0, 0, 28468916209948275649931686066133896000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28468916209948275649931686066133896000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD
      (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) /
      1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 1 = 1 then
      ((alpha 0 s * ((jointRows 0 s).map
        (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) /
          (denominator : ℚ) ^ 5 else 0 := by sorry
