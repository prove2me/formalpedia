-- Prove2me | Theorems.Thm_Smooth1Properties_below
-- name    : Smooth1Properties_below
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:01:06.122926+00:00
-- url     : https://prove2.me/theorems/d19f7cfd-c602-402f-aeb9-d6b6675b73de
-- title:
--   The smoothed cutoff equals one below the transition window: $\widetilde{1_\epsilon}(x) = 1$ for $0 < x \le 1 - \log 2 \cdot \epsilon$
-- statement:
--   Let $\nu$ be a smoothing kernel supported in $[1/2, 2]$ and of multiplicative mass one, $\int_0^\infty \nu(x)\, dx / x = 1$. For $\epsilon > 0$ let $\widetilde{1_\epsilon} = \mathrm{Smooth1}\,\nu\,\epsilon$ be the smoothed indicator of $(0, 1]$ built by multiplicative convolution with the $\epsilon$-rescaled kernel.
--
--   Then there is an explicit constant $c > 0$, namely $c = \log 2$, such that for every $\epsilon > 0$ and every $x$ with $0 < x \le 1 - c\,\epsilon$,
--
--   $$\widetilde{1_\epsilon}(x) = 1.$$
--
--   This is the plateau property of the smoothed cutoff: below the $O(\epsilon)$-wide transition window the convolution integrates the full unit mass of the kernel, so the smoothed indicator agrees exactly with the sharp one. Paired with the vanishing property above $1 + 2\log 2\cdot\epsilon$, it confines all smoothing error to a multiplicative window of width $O(\epsilon)$ around $x = 1$, which is what bounds $|\psi_\epsilon(X) - \psi(X)|$ by $O(\epsilon X \log X)$ in the smoothed Prime Number Theorem proof.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L617-L645

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

theorem Smooth1Properties_below {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    ∃ (c : ℝ), 0 < c ∧ c = Real.log 2 ∧
      ∀ (ε x) (_ : 0 < ε), 0 < x → x ≤ 1 - c * ε → Smooth1 ν ε x = 1 := by sorry
