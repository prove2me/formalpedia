-- Prove2me | Theorems.Thm_Smooth1Nonneg
-- name    : Smooth1Nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:36:25.918415+00:00
-- url     : https://prove2.me/theorems/b1f5ff5b-64f1-479a-9326-03ab649b2501
-- title:
--   Nonnegativity of the smoothed cutoff: $0 \le \widetilde{1_\epsilon}(x)$
-- statement:
--   Let $\nu$ be a smoothing kernel that is nonnegative on the positive reals, and let $\epsilon > 0$. Let $\widetilde{1_\epsilon} = \mathrm{Smooth1}\,\nu\,\epsilon$ denote the smoothed indicator of $(0,1]$ obtained by multiplicative convolution of the sharp cutoff $\mathbf{1}_{(0,1]}$ with the $\epsilon$-rescaled kernel.
--
--   Then for every $x > 0$,
--
--   $$0 \;\le\; \widetilde{1_\epsilon}(x).$$
--
--   This is the elementary positivity half of the two-sided bound $0 \le \widetilde{1_\epsilon} \le 1$: the convolution of two nonnegative functions is nonnegative. In the smoothed-Chebyshev framework it ensures the smoothed sum $\sum_n \Lambda(n)\,\widetilde{1_\epsilon}(n/X)$ is a genuine sub-sum-with-weights of von Mangoldt values, which is what makes the comparison with $\psi(X)$ a monotonicity argument.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L756-L761

import Batteries.Tactic.Lemma
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Definitions.Def_MellinCalculus_defs

open scoped ContDiff

set_option lang.lemmaCmd true

-- TODO: move near `MeasureTheory.setIntegral_prod`

-- How to deal with this coercion?... Ans: (f ·)
--- noncomputable def funCoe (f : ℝ → ℝ) : ℝ → ℂ := fun x ↦ f x

open Complex Topology Filter Real MeasureTheory Set

variable {𝕂 : Type*} [RCLike 𝕂]

-- TODO: generalize to `RCLike`

local notation (name := mellintransform) "𝓜" => mellin

-- filter-free version:

-- This lemma might not be necessary, but the RHS is supported on [0, infinity), which makes
-- results like `support_MellinConvolution_subsets` easier to apply.

/-% ** Wrong delimiters on purpose, no need to include this in the LaTeX outline
\begin{lemma}[Smooth1Properties_estimate]\label{Smooth1Properties_estimate}
\lean{Smooth1Properties_estimate}\leanok
For $\epsilon>0$,
$$
  \log2>\frac{1-2^{-\epsilon}}\epsilon
$$
\end{lemma}
%-/

theorem Smooth1Nonneg {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x) {ε x : ℝ}
    (xpos : 0 < x) (εpos : 0 < ε) : 0 ≤ Smooth1 ν ε x := by sorry
