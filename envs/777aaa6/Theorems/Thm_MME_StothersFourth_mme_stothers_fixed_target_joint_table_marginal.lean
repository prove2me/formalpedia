-- Prove2me | Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_target_joint_table_marginal
-- name    : MME.StothersFourth.mme_stothers_fixed_target_joint_table_marginal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:02:21.109747+00:00
-- url     : https://prove2.me/theorems/b9e47292-bac0-4f60-b39b-e8716129d6b8
-- title:
--   Marginals of the fixed Stothers target joint table
-- statement:
--   For every scale $m$, mode $i$, and grade $j$, summing the fixed target multiplicities over all supported joint types whose $i$-th component is $j$ gives exactly the prescribed marginal count $M_j$. In symbols,
--
--   $$
--   \sum_{\sigma\in\Omega:\,\sigma_i=j} k^*_\sigma=M_j.
--   $$
--
--   This identifies the target joint table with the common marginal profile used throughout the completion-star entropy comparison.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5, Equation (5.2) and the displayed symmetric parameter table, printed pp. 367--368, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_stothers_fixed_joint_tables

open MME BigOperators

set_option autoImplicit false

theorem MME.StothersFourth.mme_stothers_fixed_target_joint_table_marginal
    (m : ℕ) (i : Fin 3) (j : Fin 9) :
    (∑ sigma : {sigma : MME.StothersFourth.FixedHashSupportTriple // sigma.1 i = j},
      MME.StothersFourth.fixedHashTargetJointTable m sigma.1) =
        MME.StothersFourth.fixedMarginalCount m j := by
  sorry
