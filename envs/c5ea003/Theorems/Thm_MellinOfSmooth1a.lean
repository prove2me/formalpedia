-- Prove2me | Theorems.Thm_MellinOfSmooth1a
-- name    : MellinOfSmooth1a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:34:51.168823+00:00
-- url     : https://prove2.me/theorems/c779ce4e-9133-48bd-ae12-4ebaa4c54e89
-- title:
--   Mellin transform of the smoothed cutoff: $\mathcal{M}(\widetilde{1_\varepsilon})(s)=\frac{1}{s}\,\mathcal{M}\nu(\varepsilon s)$
-- statement:
--   Let $\nu\colon\mathbb{R}\to\mathbb{R}$ be a mollifier of class $C^1$ with support contained in $[1/2,2]$, let $\varepsilon>0$, and let $s\in\mathbb{C}$ with $\operatorname{Re} s>0$. Write $\widetilde{1_\varepsilon}$ (`Smooth1`$\,\nu\,\varepsilon$) for the smoothed cutoff obtained as the Mellin convolution of the sharp cutoff $\mathbf{1}_{(0,1]}$ with the delta spike $\nu_\varepsilon(x)=\nu(x^{1/\varepsilon})/\varepsilon$. Then its Mellin transform factors explicitly:
--
--   $$\mathcal{M}\bigl(\widetilde{1_\varepsilon}\bigr)(s) \;=\; \frac{1}{s}\,\mathcal{M}\nu(\varepsilon s).$$
--
--   This combines the elementary transform $\mathcal{M}(\mathbf{1}_{(0,1]})(s)=1/s$, the dilation identity $\mathcal{M}(\nu_\varepsilon)(s)=\mathcal{M}\nu(\varepsilon s)$, and the Mellin convolution theorem, with the compact support and $C^1$ regularity of $\nu$ supplying the integrability needed for the convolution-transform interchange.
--
--   The formula is the analytic heart of the smoothed Perron method: it exhibits the transform of the smoothed cutoff as the Perron kernel $1/s$ damped by the rapidly decaying factor $\mathcal{M}\nu(\varepsilon s)$, which is what allows contours to be pulled and truncated with quantitative control in the proof of the Prime Number Theorem with error term.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L813-L883

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

theorem MellinOfSmooth1a {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    {ε : ℝ} (εpos : 0 < ε) {s : ℂ} (hs : 0 < s.re) :
    𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s =
      s⁻¹ * 𝓜 (fun x ↦ (ν x : ℂ)) (ε * s) := by sorry
