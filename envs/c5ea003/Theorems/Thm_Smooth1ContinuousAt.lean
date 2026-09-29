-- Prove2me | Theorems.Thm_Smooth1ContinuousAt
-- name    : Smooth1ContinuousAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:35:35.318054+00:00
-- url     : https://prove2.me/theorems/a2d2f54b-4b25-478c-bb84-3ef9f50b3fa5
-- title:
--   Continuity of the smoothed cutoff $\widetilde{1_\epsilon}(x)$ at every positive point
-- statement:
--   Let $F$ be a smoothing kernel of class $C^1$ on $\mathbb{R}$, nonnegative on $(0, \infty)$ and supported in the interval $[1/2, 2]$. For $\epsilon > 0$, let $\widetilde{1_\epsilon} = \mathrm{Smooth1}\,F\,\epsilon$ denote the smoothed indicator of $(0, 1]$ obtained by multiplicative (Mellin) convolution of the sharp cutoff $\mathbf{1}_{(0,1]}$ with the $\epsilon$-rescaled kernel $F_\epsilon(x) = \tfrac{1}{\epsilon} F(x^{1/\epsilon})$.
--
--   Then for every $y > 0$, the function $x \mapsto \widetilde{1_\epsilon}(x)$ is continuous at $y$:
--
--   $$\lim_{x \to y} \widetilde{1_\epsilon}(x) = \widetilde{1_\epsilon}(y).$$
--
--   Continuity of the smoothed cutoff on the positive axis is one of the basic regularity facts needed to apply Mellin transform theory to it: it guarantees the integrand in $\int_0^\infty \widetilde{1_\epsilon}(x)\, x^{s-1}\, dx$ is well behaved, and it underlies the convergence and holomorphy of the Mellin transform $\mathcal{M}(\widetilde{1_\epsilon})(s)$ that drives the smoothed Chebyshev function analysis in the PNT+ proof of the Prime Number Theorem.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L931-L1013

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

theorem Smooth1ContinuousAt {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : SmoothingF.support ⊆ Icc (1 / 2) 2)
    {ε : ℝ} (εpos : 0 < ε) {y : ℝ} (ypos : 0 < y) :
    ContinuousAt (fun x ↦ Smooth1 SmoothingF ε x) y := by sorry
