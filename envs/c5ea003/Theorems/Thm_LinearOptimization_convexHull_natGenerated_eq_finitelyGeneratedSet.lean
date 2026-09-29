-- Prove2me | Theorems.Thm_LinearOptimization_convexHull_natGenerated_eq_finitelyGeneratedSet
-- name    : LinearOptimization.convexHull_natGenerated_eq_finitelyGeneratedSet
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-10T03:12:08.983706+00:00
-- url     : https://prove2.me/theorems/1cf53b37-8b97-4ef8-896a-414a98f2c8f8
-- title:
--   Convex hull of discrete ray generators
-- statement:
--   Let $x^1,\ldots,x^k\in\mathbb{R}^n$ be finitely many base points and let $w^1,\ldots,w^r\in\mathbb{R}^n$ be finitely many directions. Define the discrete generated set by choosing one base point and nonnegative integer multiples of the directions. Then its convex hull is exactly the finitely generated polyhedron obtained by allowing a convex combination of the base points and arbitrary nonnegative real multiples of the directions:
--
--   $$\operatorname{conv}\left\{x^i+\sum_{j=1}^r q_jw^j:i\in\{1,\ldots,k\},\ q_j\in\mathbb{Z}_{\ge 0}\right\}=\left\{\sum_{i=1}^k\lambda_i x^i+\sum_{j=1}^r\theta_jw^j:\lambda,\theta\ge0,\ \sum_i\lambda_i=1\right\}.$$
--
--   This is the purely convex-geometric bridge used after the integer monoid has been finitely generated.
-- source:
--   Bertsimas and Tsitsiklis, Introduction to Linear Optimization (Athena Scientific, 1997), Exercise 11.8(c)-(d), p. 525; purely formal convexification bridge for the finite integer-generator representation in Theorem 11.3, p. 496.

import Mathlib.Analysis.Convex.Combination
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_LinearOptimization_FinitelyGeneratedSet
import Theorems.Thm_LinearOptimization_finitely_generated_is_polyhedron

theorem LinearOptimization.convexHull_natGenerated_eq_finitelyGeneratedSet {n k r : ℕ}
    (x : Fin k → (Fin n → ℝ)) (w : Fin r → (Fin n → ℝ)) :
    convexHull ℝ
        {y | ∃ (i : Fin k) (q : Fin r → ℕ),
          y = x i + ∑ j, (q j : ℝ) • w j} =
      finitelyGeneratedSet x w := by sorry
