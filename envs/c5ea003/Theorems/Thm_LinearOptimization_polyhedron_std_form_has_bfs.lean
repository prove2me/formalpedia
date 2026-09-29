-- Prove2me | Theorems.Thm_LinearOptimization_polyhedron_std_form_has_bfs
-- name    : LinearOptimization.polyhedron_std_form_has_bfs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T13:55:04.591366+00:00
-- url     : https://prove2.me/theorems/60b0c22e-61d8-4784-b400-23a9fcf324a6
-- title:
--   Existence of basic feasible solutions for bounded and standard-form polyhedra
-- statement:
--   **(Corollary 2.2)** Every nonempty bounded polyhedron and every nonempty polyhedron in standard form has at least one basic feasible solution.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Corollary 2.2, p. 65

import Definitions.Def_Polyhedron
import Definitions.Def_BasicSolution


/-- **B&T Corollary 2.2 (p. 65).** Every nonempty bounded general-form
polyhedron, and every nonempty standard-form polyhedron, has at least one
basic feasible solution (with respect to its presentation). -/

theorem LinearOptimization.polyhedron_std_form_has_bfs {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    ((polyhedron A b).Nonempty → IsBoundedSet (polyhedron A b) →
      ∃ x, IsBasicFeasibleSolution (generalFormSystem A b) x) ∧
    ((stdPolyhedron A b).Nonempty →
      ∃ x, IsBasicFeasibleSolution (stdFormSystem A b) x) := by
  sorry
