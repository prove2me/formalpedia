-- Prove2me | Theorems.Thm_GoldbachKernel_normalized_complex_laplace_seven_halves
-- name    : GoldbachKernel_normalized_complex_laplace_seven_halves
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T10:23:10.813183+00:00
-- url     : https://prove2.me/theorems/ea286b15-e2ab-4376-80e3-696911014965
-- title:
--   Normalized Goldbach kernel comparison for absolute frequencies at least 7/2
-- statement:
--   Let
--
--   $$
--   g(u)=\frac{(2-u)^3(4+6u+u^2)}{30},\qquad
--   G(z)=\int_0^2g(u)e^{-zu}\,du,\qquad
--   Z(r)=\int_0^2g(u)e^{-ru}\,du.
--   $$
--
--   For real numbers $a,b,t$ satisfying $a\ge0$, $1/2\le b\le9/10$, and $|t|\ge7/2$,
--
--   $$
--   \frac{\operatorname{Re}G(-b+it)}{Z(-b)}
--   \le
--   \frac{\operatorname{Re}G(a+it)}{Z(a)}.
--   $$
--
--   The denominators are positive. This is a supporting polynomial-transform comparison for the Goldbach exceptional-set argument. It covers the outer frequency range for the stated detector shifts; the remaining inner frequency range and the density argument require separate results. No proof of strong Goldbach is asserted.
-- source:
--   Independently certified supporting polynomial-transform bound motivated by Pintz, arXiv:1804.09084v2, Section 6, Lemmas 3 and 5, especially Eq. (6.25)-(6.28), pp. 27-29, https://arxiv.org/pdf/1804.09084v2#page=28. Exact domain: a >= 0, 1/2 <= b <= 9/10, |t| >= 7/2. This statement has no upper bound on a, and is not a verbatim statement of Lemma 5. An 83-cell outward-rounded rational certificate closes the compact negative-strip sign; the analytic norm-eight tail and right-half-plane positivity complete the argument. No mathematical novelty claim or proof of strong Goldbach.

import Mathlib

open MeasureTheory
set_option autoImplicit false

theorem GoldbachKernel_normalized_complex_laplace_seven_halves (a b t : ℝ) (ha : 0 ≤ a)
    (hb_lower : (1/2:ℝ) ≤ b) (hb_upper : b ≤ 9/10)
    (ht : (7/2:ℝ) ≤ |t|) :
    ((∫ u in (0:ℝ)..2, ((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*
      Complex.exp (-(((-b:ℝ):ℂ)+(t:ℂ)*Complex.I)*(u:ℂ))) : ℂ).re /
      (∫ u in (0:ℝ)..2, ((2-u)^3*(4+6*u+u^2)/30)*Real.exp (b*u)) ≤
    ((∫ u in (0:ℝ)..2, ((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*
      Complex.exp (-((a:ℂ)+(t:ℂ)*Complex.I)*(u:ℂ))) : ℂ).re /
      (∫ u in (0:ℝ)..2, ((2-u)^3*(4+6*u+u^2)/30)*Real.exp (-a*u)) := by sorry
