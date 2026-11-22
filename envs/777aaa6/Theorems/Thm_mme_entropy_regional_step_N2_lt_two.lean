-- Prove2me | Theorems.Thm_mme_entropy_regional_step_N2_lt_two
-- name    : mme_entropy_regional_step_N2_lt_two
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-18T14:38:42.093801+00:00
-- url     : https://prove2.me/theorems/831998d3-e627-432d-b6f2-923f423f3265
-- title:
--   N=2 integer steps live below level 2
-- statement:
--   Every integer regional step with two elementary positions lives below level $2$.
--
--   The length equation already forces $lower < 3$, and level $2$ itself is impossible: at level $2$ the length equation gives $L=1$ while physical positions contain both halves of every parent occurrence. Hence only levels $0$ and $1$ carry content at $N=2$.
--
--   **Formalization Note** This combines the level bound $lower < 3$ with the level-two impossibility, both already proved nodes in the same environment.
-- source:
--   Consequence of mme_integer_regional_step_N2_level_bound and mme_entropy_regional_step_L2_N2_impossible; sizing for Alman et al., More Asymmetry, https://arxiv.org/html/2404.16349v2#S6, Section 6.

import Definitions.Def_mme_integer_regional_CW_recipe
set_option autoImplicit false

theorem mme_entropy_regional_step_N2_lt_two : forall (lower : Nat) (S : MME.RegionRealization.IntegerStep lower 2 (fun _ _ => True)), lower < 2 := by sorry
