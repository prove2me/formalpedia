-- Prove2me | Theorems.Thm_Smooth1Properties_above
-- name    : Smooth1Properties_above
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:36:51.651906+00:00
-- url     : https://prove2.me/theorems/28ca6d14-4ad5-4d3e-a738-59a2eaf5411e
-- title:
--   The smoothed cutoff vanishes above the transition window: $\widetilde{1_\epsilon}(x) = 0$ for $x \ge 1 + 2\log 2 \cdot \epsilon$
-- statement:
--   Let $\nu$ be a smoothing kernel supported in the interval $[1/2, 2]$, and for $\epsilon > 0$ let $\widetilde{1_\epsilon} = \mathrm{Smooth1}\,\nu\,\epsilon$ be the smoothed indicator of $(0, 1]$ obtained by multiplicative convolution with the $\epsilon$-rescaled kernel $\nu_\epsilon(x) = \tfrac{1}{\epsilon}\nu(x^{1/\epsilon})$.
--
--   Then there is an explicit constant $c > 0$, namely $c = 2 \log 2$, such that for every $\epsilon \in (0, 1)$ and every real $x$,
--
--   $$x \;\ge\; 1 + c\,\epsilon \quad\Longrightarrow\quad \widetilde{1_\epsilon}(x) = 0.$$
--
--   This makes precise that the smoothing only blurs the sharp cutoff $\mathbf{1}_{(0,1]}$ within a window of width $O(\epsilon)$ above $1$: since the rescaled kernel is supported where $x^{1/\epsilon} \in [1/2, 2]$, i.e. in $[2^{-\epsilon}, 2^{\epsilon}]$, the convolution cannot see any mass beyond $2^{\epsilon} \le 1 + 2\log 2 \cdot \epsilon$. Together with the companion plateau statement below $1$, it quantifies exactly how far the smoothed Chebyshev sum can differ from $\psi(X)$ — the source of the $O(\epsilon X \log X)$ comparison error in the PNT+ argument.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L698-L732

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

theorem Smooth1Properties_above {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    ∃ (c : ℝ), 0 < c ∧ c = 2 * Real.log 2 ∧
      ∀ (ε x) (_ : ε ∈ Ioo 0 1), 1 + c * ε ≤ x → Smooth1 ν ε x = 0 := by sorry
