-- Prove2me | Theorems.Thm_MellinOfSmooth1b
-- name    : MellinOfSmooth1b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:35:22.711573+00:00
-- url     : https://prove2.me/theorems/3afc0155-bd1b-48d7-8ad9-9af5a76ed602
-- title:
--   Uniform decay bound $\|\mathcal{M}(\widetilde{1_\varepsilon})(s)\| \le C/(\varepsilon\|s\|^2)$ in vertical strips
-- statement:
--   Let $\nu\colon\mathbb{R}\to\mathbb{R}$ be a mollifier of class $C^1$ with support contained in $[1/2,2]$. Then there exists a constant $C>0$, depending only on $\nu$, such that for every $\sigma_1>0$, every $s\in\mathbb{C}$ with $\sigma_1\le\operatorname{Re} s\le 2$, and every $\varepsilon\in(0,1)$, the Mellin transform of the smoothed cutoff $\widetilde{1_\varepsilon}$ (`Smooth1`$\,\nu\,\varepsilon$) satisfies
--
--   $$\left\|\mathcal{M}\bigl(\widetilde{1_\varepsilon}\bigr)(s)\right\| \;\le\; \frac{C}{\varepsilon\,\|s\|^{2}}.$$
--
--   Note the uniformity: the single constant $C$ works for all abscissae $\sigma_1>0$ simultaneously (the strip constraint $\sigma_1\le \operatorname{Re} s\le 2$ merely places $s$ in the right half-plane with bounded real part). The $\|s\|^{-2}$ decay comes from integrating by parts once against the $C^1$ mollifier: each integration by parts converts a power of $s$ into a factor $1/\varepsilon$ from differentiating the spike.
--
--   This quadratic decay in $|s|$ is exactly what makes the vertical contour integrals in the smoothed Perron formula absolutely convergent and lets the tails of the contour above height $T$ be discarded at an acceptable cost of $1/(\varepsilon T)$ — one of the two competing error sources optimized in the final PNT error term.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L887-L911

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

theorem MellinOfSmooth1b {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
    ∃ (C : ℝ) (_ : 0 < C), ∀ (σ₁ : ℝ) (_ : 0 < σ₁)
    (s) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
    ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ C * (ε * ‖s‖ ^ 2)⁻¹ := by sorry
