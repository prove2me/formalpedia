-- Prove2me | Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_exact_target_star_degree_le_power100
-- name    : MME.StothersFourth.mme_stothers_fixed_exact_target_star_degree_le_power100
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:21:35.243353+00:00
-- url     : https://prove2.me/theorems/426a583a-a82f-49fc-b19a-6581e47d56f3
-- title:
--   Power-100 completion-degree bound for exact Stothers targets
-- statement:
--   For every positive scale $m$, every exact target address, and every mode, the number of marginal-supported addresses sharing its word in that mode is at most
--
--   $$
--   \bigl(6(N+1)\bigr)^{100}D_*.
--   $$
--
--   Here $N$ is the fixed outer length and $D_*$ is the exact target completion degree. This is a convenient polynomial relaxation of the sharp $45$-table star bound, in the form consumed by the affine-hash budget.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and Equation (3.4), printed pp. 354--356, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; this is a polynomial relaxation of the proved method-of-types completion-star estimate.

import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_stothers_fixed_joint_tables

open MME BigOperators

set_option autoImplicit false

theorem MME.StothersFourth.mme_stothers_fixed_exact_target_star_degree_le_power100
    (m : ℕ) (hm : 0 < m)
    (i : Fin 3)
    (a : {a : MME.StothersFourth.FixedMarginalSupportedAddress m //
      MME.StothersFourth.FixedHasExactJointProfile a}) :
    Nat.card
        {b : MME.StothersFourth.FixedMarginalSupportedAddress m //
          b.1 i = a.1.1 i} ≤
      (6 * (MME.StothersFourth.fixedOuterLength m + 1)) ^ 100 *
        MME.StothersFourth.fixedHashTargetStarDegree m := by
  sorry
