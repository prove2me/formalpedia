-- Prove2me | Theorems.Thm_Goldbach_density_kernel_positive_moment_formula
-- name    : Goldbach.density_kernel_positive_moment_formula
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T03:21:15.504354+00:00
-- url     : https://prove2.me/theorems/abecf3c7-e36e-4a16-a980-48a4b1d2e50f
-- title:
--   An exact positive moment formula for the density detector kernel
-- statement:
--   For every natural number $n$, let
--
--   $$g(u)=\frac{(2-u)^3(4+6u+u^2)}{30},\qquad 0\le u\le2.$$
--
--   The exact moment identity is
--
--   $$\int_0^2g(u)u^n\,du
--   =\frac{4\cdot2^{n+4}}{5(n+1)(n+2)(n+3)(n+4)}
--   +\frac{6\cdot2^{n+5}}{5(n+2)(n+3)(n+4)(n+5)}
--   +\frac{2^{n+6}}{5(n+3)(n+4)(n+5)(n+6)}.$$
--
--   This positive expression is the moment formula used in the independent exact
--   rational detector audit. At $n=0$ it gives the normalization $8/9$.
--   The closed proof expands the polynomial kernel, applies Mathlib's power
--   integrals, and proves the rational identity for every natural exponent. No
--   numerical approximation or imported open theorem is used.
--
--   The kernel is from equation (3.21) of Zhao's v2:
--   https://arxiv.org/html/2511.05631v2#S3 . This elementary integration identity
--   does not prove the analytic density theorem or a Goldbach conclusion. Its
--   formalization removes one external arithmetic premise from the rational
--   Laplace enclosure program; no mathematical novelty is claimed.
-- source:
--   Exact moments of the kernel in equation (3.21), https://arxiv.org/html/2511.05631v2#S3 . Elementary integration, not a proof of the analytic density theorem; no mathematical novelty is claimed.

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open MeasureTheory
set_option autoImplicit false

theorem Goldbach.density_kernel_positive_moment_formula (n : ℕ) :
    (∫ u in (0:ℝ)..2, ((2-u)^3*(4+6*u+u^2)/30)*u^n) =
      4*(2:ℝ)^(n+4)/(5*((n:ℝ)+1)*((n:ℝ)+2)*((n:ℝ)+3)*((n:ℝ)+4)) +
      6*(2:ℝ)^(n+5)/(5*((n:ℝ)+2)*((n:ℝ)+3)*((n:ℝ)+4)*((n:ℝ)+5)) +
      (2:ℝ)^(n+6)/(5*((n:ℝ)+3)*((n:ℝ)+4)*((n:ℝ)+5)*((n:ℝ)+6)) := by sorry
