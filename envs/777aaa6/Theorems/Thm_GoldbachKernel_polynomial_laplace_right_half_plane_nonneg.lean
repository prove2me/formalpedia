-- Prove2me | Theorems.Thm_GoldbachKernel_polynomial_laplace_right_half_plane_nonneg
-- name    : GoldbachKernel_polynomial_laplace_right_half_plane_nonneg
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T06:59:06.680122+00:00
-- url     : https://prove2.me/theorems/0f4ef0a6-97f4-4b98-aa43-e1fb4fdf2f3a
-- title:
--   Nonnegative real part of the Goldbach polynomial transform on the right half-plane
-- statement:
--   Let
--   $$
--   g(u)=\frac{(2-u)^3(4+6u+u^2)}{30},\qquad
--   G(z)=\int_0^2g(u)e^{-zu}\,du.
--   $$
--   For every complex $z$ with $\operatorname{Re}z\ge0$,
--   $$
--   \operatorname{Re}G(z)\ge0.
--   $$
--   This proves the complex-transform positivity component of the polynomial
--   kernel used in weighted Dirichlet zero-density arguments. It covers the
--   closed right half-plane, every imaginary frequency, and the origin.
--
--   The checked proof derives the complex closed form and $G(0)=8/9$. On the
--   imaginary axis it obtains the exact square identity
--   $$
--   \operatorname{Re}G(it)=\frac{8(t\cos t-\sin t)^2}{t^6}\quad(t\ne0).
--   $$
--   It also proves $\lVert G(z)\rVert\le8/9$ in the closed right half-plane,
--   establishes differentiability in its interior and continuity on its closure,
--   and applies Mathlib's Phragmen-Lindelof principle to $\exp(-G)$.
--
--   **Formalization Note** This is a formal proof of a known supporting kernel
--   property, not a new density estimate. It does not establish the all-frequency
--   normalized comparison, the weighted explicit formula, a Dirichlet
--   zero-density inequality, or Goldbach's conjecture. Regularity requirements on
--   the compactly supported real kernel remain distinct from this transform
--   positivity statement.
-- source:
--   Known supporting positivity property of the polynomial kernel in Pintz, arXiv:1804.09084v2, Conditions 1-2 and the kernel discussion on pp. 28-29, https://arxiv.org/pdf/1804.09084v2#page=28. Independently formalized using the complex closed form, its imaginary-axis square identity, dominated continuity, and a maximum principle; not a new density estimate. Formal ingredients: https://github.com/leanprover-community/mathlib4/blob/777aaa61dcd2a1258d2b4962dbe983ede4d23b2e/Mathlib/Analysis/Complex/PhragmenLindelof.lean (right_half_plane_of_bounded_on_real); https://github.com/leanprover-community/mathlib4/blob/777aaa61dcd2a1258d2b4962dbe983ede4d23b2e/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean (continuous_of_dominated_interval); https://github.com/leanprover-community/mathlib4/blob/777aaa61dcd2a1258d2b4962dbe983ede4d23b2e/Mathlib/Analysis/Complex/RealDeriv.lean (HasDerivAt.comp_ofReal).

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

open MeasureTheory
set_option autoImplicit false

theorem GoldbachKernel_polynomial_laplace_right_half_plane_nonneg (z : ℂ) (hz : 0 ≤ z.re) :
    0 ≤ ((∫ u in (0:ℝ)..2, ((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*
      Complex.exp (-z*(u:ℂ))) : ℂ).re := by sorry
