-- Prove2me | Theorems.Thm_LinearOptimization_polyhedron_extreme_point_existence
-- name    : LinearOptimization.polyhedron_extreme_point_existence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T13:54:51.694382+00:00
-- url     : https://prove2.me/theorems/551d992c-f57e-49d5-9b3b-fa26a0dc5374
-- title:
--   Existence of extreme points: a polyhedron has an extreme point iff it contains no line
-- statement:
--   **(Theorem 2.6)** Suppose that the polyhedron
--
--   $$P = \{x \in \mathbb{R}^n \mid a_i'x \ge b_i,\ i = 1, \dots, m\}$$
--
--   is nonempty. Then, the following are equivalent:
--
--   - **(a)** The polyhedron $P$ has at least one extreme point.
--   - **(b)** The polyhedron $P$ does not contain a line.
--   - **(c)** There exist $n$ vectors out of the family $a_1, \dots, a_m$, which are linearly independent.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 2.6, p. 63

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Data.List.TFAE
import Definitions.Def_Polyhedron
import Definitions.Def_ContainsLine


/-- **B&T Theorem 2.6 (p. 63).** Existence of extreme points of a nonempty
general-form polyhedron: extreme point exists ⟺ no line contained ⟺ some
`n` of the constraint vectors (= rows of `A`) are linearly independent. -/

theorem LinearOptimization.polyhedron_extreme_point_existence {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hne : (polyhedron A b).Nonempty) :
    List.TFAE
      [ (Set.extremePoints ℝ (polyhedron A b)).Nonempty,
        ¬ ContainsLine (polyhedron A b),
        ∃ s : Finset (Fin m), s.card = n ∧
          LinearIndependent ℝ (fun i : s => A i.1) ] := by
  sorry
