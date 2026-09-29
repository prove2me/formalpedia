-- Prove2me | Theorems.Thm_circle_trig_quadratic_pos
-- name    : circle_trig_quadratic_pos
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-28T06:49:34.76657+00:00
-- url     : https://prove2.me/theorems/a4f8fac9-9ee5-4043-ad35-cc95003ae1aa
-- title:
--   Positivity of a degree-two trigonometric polynomial on a circle
-- statement:
--   Let $x, y, R, k, a, b, p, q, S$ be real numbers with $x^2 + y^2 = R^2$, $S \ge 0$ and $S^2 = p^2 + q^2$. If
--   $$k - R^2 S > 0 \qquad\text{and}\qquad R^2\,(a^2 + b^2) < \bigl(k - R^2 S\bigr)^2,$$
--   then
--   $$k + a x + b y + p\,(x^2 - y^2) + 2 q\, x y > 0 .$$
--
--   Writing $(x, y) = R(\cos\varphi, \sin\varphi)$, the left-hand side is the degree-two trigonometric polynomial $k + R(a\cos\varphi + b\sin\varphi) + R^2(p\cos 2\varphi + q\sin 2\varphi)$. Its first and second harmonics have amplitudes $R\sqrt{a^2+b^2}$ and $R^2 S$, so it is bounded below by $k - R\sqrt{a^2+b^2} - R^2 S$. The statement is this bound in a square-root-free form, which suits polynomial or interval certificates. In the restricted three-body problem it eliminates the momentum angle on each fiber of the Levi-Civita energy surface, where the curvature determinant is exactly such a polynomial (compare Grisa, *Exact fiber elimination for the Levi–Civita convexity gates*, 2026, Lemma 3.4).
-- source:
--   Elementary (Cauchy–Schwarz). Square-root-free form of the harmonic-amplitude bound used for fiber elimination in Grisa, Exact fiber elimination for the Levi–Civita convexity gates of the planar restricted three-body problem, Zenodo 21270420 (2026), Lemma 3.4 / Theorem 3.7; applied to Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4.

import Mathlib.Data.Real.Basic

/-- A degree-two trigonometric polynomial on a circle is positive once its constant term beats
both harmonic amplitudes (square-root free form). -/
theorem circle_trig_quadratic_pos (x y R k a b p q S : ℝ)
    (hxy : x ^ 2 + y ^ 2 = R ^ 2) (hS : 0 ≤ S) (hS2 : S ^ 2 = p ^ 2 + q ^ 2)
    (h1 : 0 < k - R ^ 2 * S) (h2 : R ^ 2 * (a ^ 2 + b ^ 2) < (k - R ^ 2 * S) ^ 2) :
    0 < k + a * x + b * y + p * (x ^ 2 - y ^ 2) + 2 * q * x * y := by sorry
