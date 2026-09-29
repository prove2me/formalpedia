-- Prove2me | Theorems.Thm_LinearOptimization_integer_hull_is_finitely_generated
-- name    : LinearOptimization.integer_hull_is_finitely_generated
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-10T03:04:09.734175+00:00
-- url     : https://prove2.me/theorems/cc9771b6-6bdd-4ba5-91aa-45ec0727abf6
-- title:
--   The integer hull is finitely generated
-- statement:
--   Let $P=\{x\in\mathbb R^n\mid Dx\ge d\}$ be a nonempty rational polyhedron presented by an integer matrix $D$ and integer vector $d$, and let $X=P\cap\mathbb Z^n$. Then the integer hull $\operatorname{CH}(X)$ is finitely generated: there are finite families $x^1,\ldots,x^k$ and $w^1,\ldots,w^r$ such that
--
--   $$
--   \operatorname{CH}(X)=\left\{\sum_{i=1}^k\lambda_i x^i+\sum_{j=1}^r\theta_jw^j\;\middle|\;\lambda_i,\theta_j\ge0,\ \sum_{i=1}^k\lambda_i=1\right\}.
--   $$
--
--   This is the finite-generation core of Meyer’s theorem. It isolates the integer-lattice argument from the reusable Minkowski–Weyl converse that every finitely generated set is a polyhedron.
--
--   **Formalization Note.** “Finitely generated” is the predicate `LinearOptimization.IsFinitelyGenerated`, using the finite-generator representation of Bertsimas–Tsitsiklis Eq. (4.6).
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 11.3, p. 496; proof outline in Exercise 11.8(a)–(d), p. 525; finite-generator form Eq. (4.6), p. 182

import Mathlib.Analysis.Convex.Hull
import Definitions.Def_LinearOptimization_LagrangeanDual
import Definitions.Def_LinearOptimization_FinitelyGeneratedSet

open Matrix

theorem LinearOptimization.integer_hull_is_finitely_generated {m n : ℕ}
    (D : Matrix (Fin m) (Fin n) ℤ) (d : Fin m → ℤ)
    (hfeas : (polyhedron (D.map ((↑) : ℤ → ℝ)) (fun i => (d i : ℝ))).Nonempty) :
    IsFinitelyGenerated
      (convexHull ℝ
        (lagrangeanIntegerSet (D.map ((↑) : ℤ → ℝ)) (fun i => (d i : ℝ)))) := by
  sorry
