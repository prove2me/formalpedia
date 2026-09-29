-- Prove2me | Definitions.Def_MellinCalculus_defs
-- name    : MellinCalculus_defs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-07-29T14:48:52.225296+00:00
-- url     : https://prove2.me/theorems/0f1c5175-6483-4d20-8774-16dbc3390b29
-- title:
--   Mellin calculus: multiplicative convolution, the delta-spike approximate identity, and the smoothed indicator $\mathrm{Smooth1}$
-- statement:
--   This bundle defines the Mellin-calculus toolkit used to smooth arithmetic cutoffs in the PNT+ project. The Mellin transform $\mathcal{M}f(s) = \int_0^\infty f(x)\,x^{s-1}\,dx$ plays the role of the Fourier transform for the multiplicative group $(0,\infty)$ with Haar measure $dx/x$.
--
--   **Main definitions.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$.
--
--   - `MellinConvolution f g` — the multiplicative convolution $(f \ast_M g)(x) = \int_0^\infty f(y)\,g(x/y)\,\frac{dy}{y}$ of $f, g : \mathbb{R} \to \mathbb{K}$. Under the Mellin transform it becomes a product: $\mathcal{M}(f \ast_M g) = \mathcal{M}f \cdot \mathcal{M}g$.
--
--   - `DeltaSpike ν ε` — the rescaled kernel $\nu_\epsilon(x) = \nu(x^{1/\epsilon})/\epsilon$ built from a fixed smooth bump $\nu$ supported in $[1/2, 2]$ with $\int_0^\infty \nu(x)\,\frac{dx}{x} = 1$. As $\epsilon \to 0^+$ this is an approximate identity concentrating at $x = 1$ in the multiplicative sense, with Mellin transform $\mathcal{M}(\nu_\epsilon)(s) = \mathcal{M}(\nu)(\epsilon s)$.
--
--   - `Smooth1 ν ε` — the smoothed indicator $\widetilde{1_\epsilon} = 1_{(0,1]} \ast_M \nu_\epsilon$, the multiplicative convolution of the sharp cutoff $1_{(0,1]}$ with the delta spike. It is a smooth function equal to $1$ well inside $(0,1)$, equal to $0$ for $x \ge 1 + O(\epsilon)$, taking values in $[0,1]$, and interpolating smoothly on a window of multiplicative width $O(\epsilon)$ around $x = 1$.
--
--   **Downstream use.** The smoothed Chebyshev function is defined as $\sum_n \Lambda(n)\,\widetilde{1_\epsilon}(n/X)$; the Mellin transform identities for $\ast_M$ and `DeltaSpike` convert it into a vertical contour integral of $(-\zeta'/\zeta)(s)\,\mathcal{M}(\widetilde{1_\epsilon})(s)\,X^s$, and the decay of $\mathcal{M}(\widetilde{1_\epsilon})$ provides the convergence and error control needed in the prime number theorem contour argument.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean (definitions vendored from this file)

import Batteries.Tactic.Lemma
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped ContDiff

set_option lang.lemmaCmd true

-- TODO: move near `MeasureTheory.setIntegral_prod`

-- How to deal with this coercion?... Ans: (f ·)
--- noncomputable def funCoe (f : ℝ → ℝ) : ℝ → ℂ := fun x ↦ f x

open Complex Topology Filter Real MeasureTheory Set

variable {𝕂 : Type*} [RCLike 𝕂]


-- TODO: generalize to `RCLike`


local notation (name := mellintransform) "𝓜" => mellin


noncomputable def MellinConvolution (f g : ℝ → 𝕂) (x : ℝ) : 𝕂 :=
  ∫ y in Ioi 0, f y * g (x / y) / y


-- filter-free version:


noncomputable def DeltaSpike (ν : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  fun x ↦ ν (x ^ (1 / ε)) / ε


noncomputable def Smooth1 (ν : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  MellinConvolution (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) (DeltaSpike ν ε)

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


