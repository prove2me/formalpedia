-- Prove2me | Theorems.Thm_GoldbachKernel_normalized_complex_laplace_small_frequency
-- name    : GoldbachKernel_normalized_complex_laplace_small_frequency
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T06:17:04.568518+00:00
-- url     : https://prove2.me/theorems/1d70a1d2-2240-4ac1-bc5b-f5417523a545
-- title:
--   Monotonicity of normalized complex Laplace real parts at bounded frequency
-- statement:
--   Let $k:\mathbb R\to\mathbb R$ be continuous and nonnegative on $[0,2]$. Define
--   $$
--   Z(r)=\int_0^2 k(u)e^{-ru}\,du,\qquad
--   G(z)=\int_0^2 k(u)e^{-zu}\,du.
--   $$
--   For real $r\le s$ and $|t|\le\pi/2$, assume $Z(r)>0$ and $Z(s)>0$. Then
--   $$
--   \frac{\operatorname{Re}G(r+it)}{Z(r)}
--   \le
--   \frac{\operatorname{Re}G(s+it)}{Z(s)}.
--   $$
--   This provides the bounded-frequency normalized-transform comparison for every such kernel. In particular, choosing $r=-b$ and $s=a$ with $a,b\ge0$ gives that comparison between a negative and a nonnegative real shift. The statement includes zero frequency, negative frequencies, and equality of the shifts.
--
--   This is a supporting analytic kernel lemma for weighted zero-density arguments. It does not establish the comparison at arbitrary frequencies, nonnegative real parts throughout a complex half-plane, or any Dirichlet zero-density estimate.
--
--   **Formalization Note** The positive normalizing integrals are explicit assumptions; the theorem needs no L-functions or modulus threshold. It is a checked generalization of the bounded-frequency part of Pintz's normalized-transform comparison, not a new mathematical density result.
-- source:
--   Pintz, arXiv:1804.09084v2, Lemma 4, pp. 28-29, https://arxiv.org/pdf/1804.09084v2#page=28. Independently checked continuous-kernel, ordered-real-shift generalization of the bounded-frequency comparison; not full Condition 2. Formal ingredients: https://github.com/leanprover-community/mathlib4/blob/777aaa61dcd2a1258d2b4962dbe983ede4d23b2e/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean (integral_nonneg, integral_add, integral_sub, ContinuousLinearMap.intervalIntegral_comp_comm); https://github.com/leanprover-community/mathlib4/blob/777aaa61dcd2a1258d2b4962dbe983ede4d23b2e/Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean (antitoneOn_cos).

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

open MeasureTheory Set
set_option autoImplicit false

theorem GoldbachKernel_normalized_complex_laplace_small_frequency (kernel : ℝ → ℝ) (hk : Continuous kernel)
    (hkpos : ∀ u ∈ Icc (0:ℝ) 2, 0 ≤ kernel u)
    (r s frequency : ℝ) (hrs : r ≤ s) (ht : |frequency| ≤ Real.pi/2)
    (hrden : 0 < ∫ u in (0:ℝ)..2, kernel u*Real.exp (-r*u))
    (hsden : 0 < ∫ u in (0:ℝ)..2, kernel u*Real.exp (-s*u)) :
    ((∫ u in (0:ℝ)..2, (kernel u:ℂ)*Complex.exp
      (-((r:ℂ)+(frequency:ℂ)*Complex.I)*(u:ℂ))) : ℂ).re /
      (∫ u in (0:ℝ)..2, kernel u*Real.exp (-r*u)) ≤
    ((∫ u in (0:ℝ)..2, (kernel u:ℂ)*Complex.exp
      (-((s:ℂ)+(frequency:ℂ)*Complex.I)*(u:ℂ))) : ℂ).re /
      (∫ u in (0:ℝ)..2, kernel u*Real.exp (-s*u)) := by sorry
