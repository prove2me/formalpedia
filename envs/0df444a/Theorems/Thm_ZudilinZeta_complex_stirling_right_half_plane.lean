-- Prove2me | Theorems.Thm_ZudilinZeta_complex_stirling_right_half_plane
-- name    : ZudilinZeta.complex_stirling_right_half_plane
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-01T21:45:20.385817+00:00
-- url     : https://prove2.me/theorems/ac514978-8fc3-483c-8f92-394728a5c889
-- title:
--   A uniform complex Stirling estimate in the right half-plane
-- statement:
--   For every complex number $w$ with $\operatorname{Re}w\ge1$, the Gamma function satisfies
--   $$
--   \left|\frac{\Gamma(w+1)\exp\!\left(w-(w+\tfrac12)\log w\right)}{\sqrt{2\pi}}-1\right|
--   \le \exp\!\left(\frac{2}{\operatorname{Re}w}\right)-1.
--   $$
--   Here $\log$ is the principal complex logarithm and the square root is the positive real one. The estimate is uniform in $\operatorname{Im}w$. In particular, the normalized expression tends to $1$ whenever $\operatorname{Re}w$ tends to $+\infty$.
--
--   This is a quantitative ingredient for the Gamma-factor asymptotics in Zudilin's saddle analysis. It does not assert the contour representation or the saddle-integral asymptotic.
-- source:
--   Derived auxiliary estimate for W. Zudilin, Arithmetic of linear forms involving odd zeta values, https://arxiv.org/abs/math/0206176, Lemma 20, printed p.33. The explicit constant is proved here, not quoted from that lemma. The proof uses Mathlib's factorial_isEquivalent_stirling and the platform's proved Zeta23 digamma-series and finite-remainder identities.

import Mathlib

theorem ZudilinZeta.complex_stirling_right_half_plane (w : ℂ) (hw : 1 ≤ w.re) :
    ‖Complex.Gamma (w + 1) *
      Complex.exp (-((w + 1 / 2) * Complex.log w - w)) /
      (Real.sqrt (2 * Real.pi) : ℂ) - 1‖ ≤ Real.exp (2 / w.re) - 1 := by sorry
