-- Prove2me | Theorems.Thm_Smooth1Properties_estimate
-- name    : Smooth1Properties_estimate
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:36:38.678087+00:00
-- url     : https://prove2.me/theorems/3e34621f-9202-4aa5-b432-6b3aee5f6a41
-- title:
--   Elementary estimate $(1 - 2^{-\epsilon})/\epsilon < \log 2$ for all $\epsilon > 0$
-- statement:
--   For every real $\epsilon > 0$, the difference quotient of the function $\epsilon \mapsto 2^{-\epsilon}$ at the origin is strictly below its limiting slope:
--
--   $$\frac{1 - 2^{-\epsilon}}{\epsilon} \;<\; \log 2.$$
--
--   Equivalently, $2^{-\epsilon} > 1 - \epsilon \log 2$ for all $\epsilon > 0$ — the strict convexity of the exponential function makes it lie strictly above its tangent line at $0$.
--
--   This small real-analytic inequality calibrates the transition-window constants of the smoothed cutoff $\widetilde{1_\epsilon}$: it converts the support bound $2^{\pm\epsilon}$ of the rescaled smoothing kernel into the linear-in-$\epsilon$ bounds $1 - \log 2 \cdot \epsilon$ and $1 + 2\log 2 \cdot \epsilon$ that delimit where the smoothed indicator is exactly $1$ or exactly $0$. It is a reusable convexity estimate independent of the surrounding number theory.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L579-L605

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

theorem Smooth1Properties_estimate {ε : ℝ} (εpos : 0 < ε) :
    (1 - 2 ^ (-ε)) / ε < Real.log 2 := by sorry
