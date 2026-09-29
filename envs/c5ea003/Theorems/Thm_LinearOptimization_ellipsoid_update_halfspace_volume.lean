-- Prove2me | Theorems.Thm_LinearOptimization_ellipsoid_update_halfspace_volume
-- name    : LinearOptimization.ellipsoid_update_halfspace_volume
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-06T14:42:36.599265+00:00
-- url     : https://prove2.me/theorems/8f079865-b60f-4204-aa5c-1fc48dcfb0b2
-- title:
--   Ellipsoid update: the half-ellipsoid is covered with volume ratio $< e^{-1/(2(n+1))}$
-- statement:
--   **(Theorem 8.1, p. 366 — the key geometric result behind the ellipsoid method)** Let $E = E(\mathbf{z}, D)$ be an ellipsoid in $\mathbb{R}^n$ ($n \ge 2$; see design_note), and let $\mathbf{a}$ be a nonzero $n$-vector. Consider the halfspace $H = \{\mathbf{x} \in \mathbb{R}^n \mid \mathbf{a}'\mathbf{x} \ge \mathbf{a}'\mathbf{z}\}$ and let
--
--   $$\bar{\mathbf{z}} = \mathbf{z} + \frac{1}{n+1}\frac{D\mathbf{a}}{\sqrt{\mathbf{a}'D\mathbf{a}}}, \qquad \bar{D} = \frac{n^2}{n^2-1}\left(D - \frac{2}{n+1}\frac{D\mathbf{a}\mathbf{a}'D}{\mathbf{a}'D\mathbf{a}}\right).$$
--
--   The matrix $\bar{D}$ is symmetric and positive definite and thus $E' = E(\bar{\mathbf{z}}, \bar{D})$ is an ellipsoid. Moreover,
--
--   - **(a)** $E \cap H \subset E'$,
--   - **(b)** $\mathrm{Vol}(E') < e^{-1/(2(n+1))}\,\mathrm{Vol}(E)$.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 8.1, p. 366

import Definitions.Def_LinearOptimization_EllipsoidMethod


open Matrix MeasureTheory

/-- **Bertsimas & Tsitsiklis, Theorem 8.1 (p. 366).** Half-ellipsoid covered by a strictly
smaller ellipsoid: `D̄` is positive definite (and symmetric),
`E(z, D) ∩ {x | a'x ≥ a'z} ⊆ E(z̄, D̄)`, and
`Vol(E(z̄, D̄)) < e^{−1/(2(n+1))} · Vol(E(z, D))`. -/

theorem LinearOptimization.ellipsoid_update_halfspace_volume {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    (ellipsoidUpdateMatrix D a).PosDef ∧
    ellipsoid z D ∩ {x | a ⬝ᵥ z ≤ a ⬝ᵥ x} ⊆
      ellipsoid (ellipsoidUpdateCenter z D a) (ellipsoidUpdateMatrix D a) ∧
    volume (ellipsoid (ellipsoidUpdateCenter z D a)
        (ellipsoidUpdateMatrix D a)) <
      ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * ((n : ℝ) + 1)))) *
        volume (ellipsoid z D) := by
  sorry
