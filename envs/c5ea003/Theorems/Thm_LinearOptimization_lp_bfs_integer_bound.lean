-- Prove2me | Theorems.Thm_LinearOptimization_lp_bfs_integer_bound
-- name    : LinearOptimization.lp_bfs_integer_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-06T14:42:44.856863+00:00
-- url     : https://prove2.me/theorems/640d71b3-dcf7-49ab-955d-49af948ac751
-- title:
--   Extreme points of integer-data polyhedra are bounded by $(nU)^n$
-- statement:
--   **(Lemma 8.2, p. 373)** Let $A$ be an $m \times n$ integer matrix and let $\mathbf{b}$ be a vector in $\mathbb{R}^m$ [with integer entries]. Let $U$ be the largest absolute value of the entries in $A$ and $\mathbf{b}$.
--
--   - **(a)** Every extreme point of the polyhedron $P = \{\mathbf{x} \in \mathbb{R}^n \mid A\mathbf{x} \ge \mathbf{b}\}$ satisfies
--
--     $$-(nU)^n \le x_j \le (nU)^n, \qquad j = 1, \dots, n.$$
--
--   - **(b)** Every extreme point of the standard form polyhedron $P = \{\mathbf{x} \in \mathbb{R}^n \mid A\mathbf{x} = \mathbf{b},\ \mathbf{x} \ge \mathbf{0}\}$ satisfies
--
--     $$-(mU)^m \le x_j \le (mU)^m, \qquad j = 1, \dots, n.$$
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Lemma 8.2, p. 373

import Mathlib.Analysis.Convex.Extreme
import Definitions.Def_Polyhedron


open Matrix

/-- **Bertsimas & Tsitsiklis, Lemma 8.2 (p. 373).** Integer-data bound on extreme points:
(a) each coordinate of an extreme point of `{x | Ax ≥ b}` lies in
`[−(nU)ⁿ, (nU)ⁿ]`; (b) each coordinate of an extreme point of
`{x | Ax = b, x ≥ 0}` lies in `[−(mU)ᵐ, (mU)ᵐ]`. -/

theorem LinearOptimization.lp_bfs_integer_bound {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (U : ℤ)
    (hA : ∀ i j, |A i j| ≤ U) (hb : ∀ i, |b i| ≤ U) :
    (∀ x ∈ Set.extremePoints ℝ
        (polyhedron (A.map ((↑) : ℤ → ℝ)) (fun i => (b i : ℝ))),
      ∀ j, -(((n : ℝ) * (U : ℝ)) ^ n) ≤ x j ∧
        x j ≤ ((n : ℝ) * (U : ℝ)) ^ n) ∧
    (∀ x ∈ Set.extremePoints ℝ
        (stdPolyhedron (A.map ((↑) : ℤ → ℝ)) (fun i => (b i : ℝ))),
      ∀ j, -(((m : ℝ) * (U : ℝ)) ^ m) ≤ x j ∧
        x j ≤ ((m : ℝ) * (U : ℝ)) ^ m) := by
  sorry
