-- Prove2me | Theorems.Thm_MeasureTheory_integral_comp_mul_left_I0i_haar
-- name    : MeasureTheory.integral_comp_mul_left_I0i_haar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:35:48.39989+00:00
-- url     : https://prove2.me/theorems/54c7d384-b75b-4c70-8f7f-a13a30bd87ce
-- title:
--   Invariance of the Haar integral $\int_0^\infty f(y)\,dy/y$ under left scaling $y\mapsto ay$
-- statement:
--   Let $f\colon\mathbb{R}\to\mathbb{K}$ be a function into a normed field (the scalar field of the development), and let $a>0$. Then
--
--   $$\int_0^{\infty} f(a\,y)\,\frac{dy}{y} \;=\; \int_0^{\infty} f(y)\,\frac{dy}{y}.$$
--
--   This expresses the defining property of the measure $dy/y$ as the Haar measure of the multiplicative group $(0,\infty)$: it is invariant under the dilations $y\mapsto ay$ for every $a>0$. No integrability hypothesis is required — the identity is an instance of a measure-preserving change of variables for Bochner integrals.
--
--   It is the basic substitution rule of the Mellin calculus developed here: rescaling the argument of a function costs nothing against the multiplicative Haar measure, which is what makes the Mellin transform interact so cleanly with dilations, delta-spike mollifiers $\nu_\varepsilon(x)=\nu(x^{1/\varepsilon})/\varepsilon$, and multiplicative convolutions.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L50-L53

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

theorem MeasureTheory.integral_comp_mul_left_I0i_haar
    (f : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
    ∫ (y : ℝ) in Ioi 0, f (a * y) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by sorry
