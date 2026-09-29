-- Prove2me | Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_mode_joint_table_fiber_card
-- name    : MME.StothersFourth.mme_stothers_fixed_mode_joint_table_fiber_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:54:29.586887+00:00
-- url     : https://prove2.me/theorems/da84361c-04b0-4d9f-8b07-5958e0f3ab89
-- title:
--   Exact cardinality of a fixed-mode Stothers joint-table fiber
-- statement:
--   Fix one mode word of a marginal-supported Stothers address, and prescribe a supported joint table $k$ with the same nine-grade marginal in all three modes. The number of marginal-supported addresses completing the fixed word and realizing exactly $k$ is
--
--   $$
--   \frac{\prod_{j=0}^{8} M_j!}{\prod_{\sigma\in\Omega} k_\sigma!},
--   $$
--
--   where $M_j$ are the prescribed marginal counts and $\Omega$ is the $45$-cell supported-triple set. This is the exact row-by-row multinomial enumeration underlying the completion-star argument.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and Equation (3.4), printed pp. 354--356, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; this is the exact multinomial fiber count used before the entropy estimate.

import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_stothers_fixed_joint_tables

open MME BigOperators

set_option autoImplicit false

theorem MME.StothersFourth.mme_stothers_fixed_mode_joint_table_fiber_card
    (m : ℕ)
    (a : MME.StothersFourth.FixedMarginalSupportedAddress m) (i : Fin 3)
    (k : MME.StothersFourth.FixedHashJointMultiplicityTable)
    (hkMarginal : ∀ l : Fin 3, ∀ j : Fin 9,
      (∑ sigma : {sigma : MME.StothersFourth.FixedHashSupportTriple // sigma.1 l = j},
        k sigma.1) = MME.StothersFourth.fixedMarginalCount m j) :
    Nat.card
        {b : MME.StothersFourth.FixedMarginalSupportedAddress m //
          b.1 i = a.1 i ∧
            MME.StothersFourth.fixedHashJointTable b = k} =
      (∏ j : Fin 9,
          (MME.StothersFourth.fixedMarginalCount m j).factorial) /
        ∏ sigma : MME.StothersFourth.FixedHashSupportTriple,
          (k sigma).factorial := by
  sorry
