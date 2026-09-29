-- Prove2me | Theorems.Thm_LinearOptimization_lp_basic_solutions_finite
-- name    : LinearOptimization.lp_basic_solutions_finite
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T13:54:36.662467+00:00
-- url     : https://prove2.me/theorems/7deeb436-4366-4699-9be6-2a283acfbc4f
-- title:
--   Finiteness of basic solutions
-- statement:
--   **(Corollary 2.1)** Given a finite number of linear inequality constraints, there can only be a finite number of basic or basic feasible solutions.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Corollary 2.1, p. 52

import Mathlib.Data.Set.Finite.Basic
import Definitions.Def_BasicSolution


/-- **B&T Corollary 2.1 (p. 52).** A finite family of linear constraints
admits only finitely many basic solutions, and hence only finitely many
basic feasible solutions. -/

theorem LinearOptimization.lp_basic_solutions_finite {ι : Type} [Fintype ι] {n : ℕ}
    (C : ι → LinearConstraint n) :
    {x | IsBasicSolution C x}.Finite ∧
    {x | IsBasicFeasibleSolution C x}.Finite := by
  sorry
