-- Prove2me | Theorems.Thm_GoldbachKernel_normalized_complex_laplace_tail_eight
-- name    : GoldbachKernel_normalized_complex_laplace_tail_eight
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T08:09:41.23243+00:00
-- url     : https://prove2.me/theorems/9a468b7c-cc95-4a4a-9872-c665fdac3d49
-- title:
--   Normalized Goldbach kernel comparison for frequencies at least eight
-- statement:
--   Let
--
--   $$g(u)=\frac{(2-u)^3(4+6u+u^2)}{30},\qquad
--   G(z)=\int_0^2g(u)e^{-zu}\,du,\qquad
--   Z(r)=\int_0^2g(u)e^{-ru}\,du.$$
--
--   For all real $a,b,t$ with $a\ge0$, $1/2\le b\le1$ and $|t|\ge8$,
--
--   $$\frac{\operatorname{Re}G(-b+it)}{Z(-b)}
--   \le\frac{\operatorname{Re}G(a+it)}{Z(a)}.$$
--
--   The normalizers are strictly positive. This supporting kernel estimate covers the large-frequency portion of the normalized-transform comparison used in the Goldbach density argument. It leaves the middle-frequency range separate and does not imply strong Goldbach. The threshold improves the earlier local formal bound of 16; no mathematical novelty claim is made.
-- source:
--   Supporting polynomial-transform estimate for Pintz, arXiv:1804.09084v2, Conditions 1-2 and Lemmas 1-5, pp. 28-30, https://arxiv.org/pdf/1804.09084v2#page=28. Independently formalized analytic tail refinement to frequency eight; no novelty claim and no middle-frequency result. Formal half-plane positivity uses Mathlib PhragmenLindelof.right_half_plane_of_bounded_on_real at revision 777aaa61dcd2a1258d2b4962dbe983ede4d23b2e.

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

open MeasureTheory
set_option autoImplicit false

theorem GoldbachKernel_normalized_complex_laplace_tail_eight
    (a b t : ℝ) (ha : 0 ≤ a) (hb_lower : (1/2:ℝ) ≤ b)
    (hb_upper : b ≤ 1) (ht : 8 ≤ |t|) :
    ((∫ u in (0:ℝ)..2, ((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*
      Complex.exp (-(((-b:ℝ):ℂ)+(t:ℂ)*Complex.I)*(u:ℂ))) : ℂ).re /
      (∫ u in (0:ℝ)..2, ((2-u)^3*(4+6*u+u^2)/30)*Real.exp (-(-b)*u)) ≤
    ((∫ u in (0:ℝ)..2, ((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*
      Complex.exp (-((a:ℂ)+(t:ℂ)*Complex.I)*(u:ℂ))) : ℂ).re /
      (∫ u in (0:ℝ)..2, ((2-u)^3*(4+6*u+u^2)/30)*Real.exp (-a*u)) := by sorry
