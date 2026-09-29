-- Prove2me | Theorems.Thm_MellinOfSmooth1c
-- name    : MellinOfSmooth1c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:00:41.767927+00:00
-- url     : https://prove2.me/theorems/55628648-c5c3-478c-8910-3c8650339d36
-- title:
--   The smoothed-cutoff transform at $s=1$ is $1+O(\varepsilon)$ as $\varepsilon\to0^+$
-- statement:
--   Let $\nu\colon\mathbb{R}\to\mathbb{R}$ be a mollifier of class $C^1$ with support contained in $[1/2,2]$ and total multiplicative mass one:
--
--   $$\int_0^{\infty} \nu(x)\,\frac{dx}{x} \;=\; 1.$$
--
--   Then the Mellin transform of the smoothed cutoff $\widetilde{1_\varepsilon}$ (`Smooth1`$\,\nu\,\varepsilon$), evaluated at $s=1$, tends to $1$ at rate $O(\varepsilon)$: as $\varepsilon\to 0^{+}$,
--
--   $$\mathcal{M}\bigl(\widetilde{1_\varepsilon}\bigr)(1) - 1 \;=\; O(\varepsilon).$$
--
--   (Formally: the function $\varepsilon\mapsto \mathcal{M}(\widetilde{1_\varepsilon})(1)-1$ is big-O of the identity function along the filter of positive numbers approaching $0$.)
--
--   Since $\mathcal{M}(\widetilde{1_\varepsilon})(1)=\mathcal{M}\nu(\varepsilon)$ by the factorization $\mathcal{M}(\widetilde{1_\varepsilon})(s)=s^{-1}\mathcal{M}\nu(\varepsilon s)$, this is a first-order Taylor statement at $\varepsilon=0$ with the mass-one normalization giving the value $1$ at the origin. In the PNT contour argument, the residue of the integrand at $s=1$ is $X\cdot\mathcal{M}(\widetilde{1_\varepsilon})(1)$; this lemma converts that into the clean main term $X$ up to an error $O(\varepsilon X)$, which is then balanced against the contour errors when $\varepsilon$ is chosen as a function of $X$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L916-L927

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

theorem MellinOfSmooth1c {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    (fun ε ↦ 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 - 1) =O[𝓝[>]0] id := by sorry
