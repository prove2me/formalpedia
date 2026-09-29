-- Prove2me | Theorems.Thm_Smooth1MellinConvergent
-- name    : Smooth1MellinConvergent
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:01:54.955046+00:00
-- url     : https://prove2.me/theorems/6be92231-1873-4dae-a4fa-96855878be98
-- title:
--   Convergence of the Mellin transform of the smoothed cutoff for $\mathrm{Re}(s) > 0$
-- statement:
--   Let $\Psi$ be a smoothing kernel of class $C^1$, supported in $[1/2, 2]$, nonnegative on $(0, \infty)$, and of multiplicative mass one, $\int_0^\infty \Psi(x)\, dx / x = 1$. Fix $\epsilon \in (0, 1)$ and let $\widetilde{1_\epsilon} = \mathrm{Smooth1}\,\Psi\,\epsilon$ be the associated smoothed indicator of $(0, 1]$.
--
--   Then for every complex number $s$ with $\mathrm{Re}(s) > 0$, the Mellin integral of the smoothed cutoff converges: the function $x \mapsto \widetilde{1_\epsilon}(x)\, x^{s-1}$ is integrable on $(0, \infty)$, so that
--
--   $$\mathcal{M}\big(\widetilde{1_\epsilon}\big)(s) = \int_0^\infty \widetilde{1_\epsilon}(x)\, x^{s - 1}\, dx$$
--
--   is well defined.
--
--   Convergence holds in the full right half-plane because $\widetilde{1_\epsilon}$ is bounded, vanishes for $x \ge 1 + O(\epsilon)$, and equals $1$ only on a bounded interval near the origin, where $x^{s-1}$ is integrable for $\mathrm{Re}(s) > 0$. This is the prerequisite for using $\mathcal{M}(\widetilde{1_\epsilon})(s)$ as the test function in the contour-integral representation of the smoothed Chebyshev function.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L1018-L1039

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

theorem Smooth1MellinConvergent {Ψ : ℝ → ℝ} {ε : ℝ} (diffΨ : ContDiff ℝ 1 Ψ)
    (suppΨ : Ψ.support ⊆ Icc (1 / 2) 2) (hε : ε ∈ Ioo 0 1)
    (Ψnonneg : ∀ x > 0, 0 ≤ Ψ x) (mass_one : ∫ x in Ioi 0, Ψ x / x = 1)
    {s : ℂ} (hs : 0 < s.re) : MellinConvergent (fun x ↦ (Smooth1 Ψ ε x : ℂ)) s := by sorry
