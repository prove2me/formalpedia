-- Prove2me | Theorems.Thm_Smooth1LeOne
-- name    : Smooth1LeOne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:36:13.386288+00:00
-- url     : https://prove2.me/theorems/bda385b3-f3bf-4c22-9345-837d33c524d1
-- title:
--   The smoothed cutoff is bounded above by one: $\widetilde{1_\epsilon}(x) \le 1$
-- statement:
--   Let $\nu$ be a smoothing kernel that is nonnegative on $(0, \infty)$ and has total multiplicative mass one:
--
--   $$\int_0^\infty \frac{\nu(x)}{x}\, dx = 1.$$
--
--   For $\epsilon > 0$, let $\widetilde{1_\epsilon} = \mathrm{Smooth1}\,\nu\,\epsilon$ denote the smoothed indicator of $(0, 1]$ built from $\nu$ by multiplicative convolution with the $\epsilon$-rescaled kernel.
--
--   Then for every $x > 0$,
--
--   $$\widetilde{1_\epsilon}(x) \;\le\; 1.$$
--
--   Together with the companion nonnegativity statement, this pins the smoothed cutoff to the range $[0, 1]$, exactly as for the sharp indicator it approximates. In the smoothed-Chebyshev argument for the Prime Number Theorem this bound is what allows the smoothed sum $\sum_n \Lambda(n)\, \widetilde{1_\epsilon}(n/X)$ to be compared term-by-term with the Chebyshev function $\psi(X)$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L779-L809

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

theorem Smooth1LeOne {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (εpos : 0 < ε) {x : ℝ} (xpos : 0 < x) :
    Smooth1 ν ε x ≤ 1 := by sorry
