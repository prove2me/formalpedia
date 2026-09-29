-- Prove2me | Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_hash_degree_exponential_budget
-- name    : MME.StothersFourth.mme_stothers_fixed_hash_degree_exponential_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:32:18.050839+00:00
-- url     : https://prove2.me/theorems/e9f31f78-f1cb-4d4e-ba15-ba16cd1031ff
-- title:
--   Exponential budget for the fixed Stothers completion degree
-- statement:
--   At every positive fixed-profile scale, the polynomially relaxed exact-target completion degree obeys
--
--   $$
--   \bigl(6(N+1)\bigr)^{100}D_*\le 5^{1000N}.
--   $$
--
--   This is the exponential budget needed to instantiate the bounded-degree affine-hash and Behrend pruning argument.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and Equation (3.4), printed pp. 354--356, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; the constants are a deliberately loose explicit absorption of the completion degree into the exponential hash budget.

import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_stothers_fixed_joint_tables

open MME BigOperators

set_option autoImplicit false

theorem MME.StothersFourth.mme_stothers_fixed_hash_degree_exponential_budget
    (m : ℕ) (hm : 0 < m) :
    let N := MME.StothersFourth.fixedOuterLength m
    (6 * (N + 1)) ^ 100 *
        MME.StothersFourth.fixedHashTargetStarDegree m ≤
      5 ^ (1000 * N) := by
  sorry
