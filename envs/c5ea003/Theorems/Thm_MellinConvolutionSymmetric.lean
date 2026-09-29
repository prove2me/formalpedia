-- Prove2me | Theorems.Thm_MellinConvolutionSymmetric
-- name    : MellinConvolutionSymmetric
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:33:45.832362+00:00
-- url     : https://prove2.me/theorems/e3002596-d54e-4b9e-bd3e-0a9236dab8cb
-- title:
--   Commutativity of Mellin (multiplicative) convolution: $(f\ast g)(x)=(g\ast f)(x)$ for $x>0$
-- statement:
--   Let $f,g\colon\mathbb{R}\to\mathbb{K}$ be functions into a normed field (the scalar field of the development), and let $x>0$. The Mellin (multiplicative) convolution is defined by
--
--   $$(f\ast g)(x) \;=\; \int_0^{\infty} f(y)\,g\!\left(\frac{x}{y}\right)\frac{dy}{y}.$$
--
--   The theorem asserts that it is symmetric at every positive point:
--
--   $$(f\ast g)(x) \;=\; (g\ast f)(x).$$
--
--   The proof idea (not part of the statement) is the substitution $y\mapsto x/y$, which preserves the multiplicative Haar measure $dy/y$ on $(0,\infty)$; accordingly no integrability hypothesis is needed — the two Bochner integrals are equal by a measure-preserving change of variables.
--
--   Mellin convolution is the multiplicative-group analogue of ordinary convolution, and this commutativity is used freely in the smoothing arguments of the PNT proof: the smoothed cutoff $\widetilde{1_\varepsilon}$ is built as a Mellin convolution of the sharp cutoff $\mathbf{1}_{(0,1]}$ with a delta-spike mollifier, and symmetry allows the two factors to be exchanged at will.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L246-L255

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

theorem MellinConvolutionSymmetric (f g : ℝ → 𝕂) {x : ℝ} (xpos : 0 < x) :
    MellinConvolution f g x = MellinConvolution g f x := by sorry
