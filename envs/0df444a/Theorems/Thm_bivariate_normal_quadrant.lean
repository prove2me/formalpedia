-- Prove2me | Theorems.Thm_bivariate_normal_quadrant
-- name    : bivariate_normal_quadrant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T19:19:40.601243+00:00
-- url     : https://prove2.me/theorems/5e28591c-ed29-4d8d-b5d2-f45399498d7f
-- title:
--   Bivariate normal quadrant: $\\mathbb{P}(X>0,Y>0)=\\tfrac14+\\arcsin(t)/(2\\pi)$
-- statement:
--   The positive-quadrant integral of the standard bivariate normal density with correlation $t$.
--
--   Let $t \in (-1,1)$ and let
--   $$f_t(x,y) = \frac{1}{2\pi\sqrt{1-t^2}}\exp\!\Bigl(-\frac{x^2 - 2txy + y^2}{2(1-t^2)}\Bigr)$$
--   be the standard bivariate normal density with correlation $t$ (unit variances, zero means). Then
--   $$\int_0^\infty\!\!\int_0^\infty f_t(x,y)\,dy\,dx \;=\; \frac14 + \frac{\arcsin t}{2\pi}.$$
--
--   Equivalently, if $(X,Y)$ are standard jointly Gaussian with $\mathrm{Cov}(X,Y) = t$, then
--   $\mathbb{P}(X>0,\,Y>0) = \tfrac14 + \arcsin(t)/(2\pi)$. The formula shows the quadrant probability is affine in $\arcsin t$: $\tfrac14$ at independence, $\tfrac12$ in the perfect-correlation limit, and $0$ at $t = -1$.
--
--   **Role in the campaign.** This is the two-dimensional calculation underneath Goemans–Williamson hyperplane rounding. Writing $(X,Y) = (Z_1, tZ_1 + \sqrt{1-t^2}Z_2)$, the quadrant is the wedge between the positive $Z_1$-axis and the ray of slope $-t/\sqrt{1-t^2}$, whose angular measure is $\tfrac\pi2 + \arcsin t$; for the rotation-invariant standard Gaussian in the plane a wedge of angle $\theta$ has probability $\theta/(2\pi)$, and the radial part integrates to $1$. Via $\mathbb{P}(\text{sign differs}) = 2(\tfrac14 - \dots)$ it yields $\mathbb{E}[\operatorname{sign}X\operatorname{sign}Y] = 1 - 2\arccos(t)/\pi$, the per-edge identity of `QuantumMaxCutEnergy.gw_rounding_expectation`.
--
--   **Formalization Note.** Stated as an explicit two-dimensional integral of the density over `Set.Ioi 0 × Set.Ioi 0` in `ℝ`, with no probability-space primitives. A proof route available in Mathlib: `MeasureTheory.integral_comp_polarCoord_symm` (polar coordinates), `MeasureTheory.integral_gaussian` (the radial integral), and the trigonometric identity $\arctan\bigl(t/\sqrt{1-t^2}\bigr) = \arcsin t$ on $(-1,1)$.
-- source:
--   Classical bivariate normal orthant formula; the form used in Michel X. Goemans and David P. Williamson, Improved Approximation Algorithms for Maximum Cut and Satisfiability Problems Using Semidefinite Programming, J. ACM 42 (1995), https://doi.org/10.1145/227683.227684 , Section 3 (hyperplane rounding); see also M. Abramowitz and I. A. Stegun, Handbook of Mathematical Functions, Eq. 26.3.19 and Section 26.3 (orthant probabilities)

import Mathlib
open scoped BigOperators

theorem bivariate_normal_quadrant (t : ℝ) (ht1 : -1 < t) (ht2 : t < 1) :
    ∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
        (1 / (2 * Real.pi * Real.sqrt (1 - t ^ 2))) *
          Real.exp (-(x ^ 2 - 2 * t * x * y + y ^ 2) / (2 * (1 - t ^ 2)))
      = 1 / 4 + Real.arcsin t / (2 * Real.pi) := by sorry
