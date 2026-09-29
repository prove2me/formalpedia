-- Prove2me | Theorems.Thm_MeasureTheory_integral_comp_inv_I0i_haar
-- name    : MeasureTheory.integral_comp_inv_I0i_haar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:33:19.985588+00:00
-- url     : https://prove2.me/theorems/acd91acf-a949-44fc-9346-b51b60f32b91
-- title:
--   Invariance of the Haar integral $\int_0^\infty f(y)\,dy/y$ under inversion $y\mapsto 1/y$
-- statement:
--   Let $f\colon\mathbb{R}\to\mathbb{K}$ be a function into a normed field (the scalar field of the development). Then
--
--   $$\int_0^{\infty} f\!\left(\frac{1}{y}\right)\frac{dy}{y} \;=\; \int_0^{\infty} f(y)\,\frac{dy}{y}.$$
--
--   The measure $dy/y$ is the Haar measure of the multiplicative group $(0,\infty)$, and $y\mapsto 1/y$ is the group inversion, which preserves Haar measure on an abelian group; hence the substitution leaves the integral unchanged. No integrability hypothesis is needed, since the equality follows from a measure-preserving change of variables at the level of Bochner integrals.
--
--   Together with its companions (scaling $y\mapsto ay$, $y\mapsto ya$, and $y\mapsto a/y$), this lemma supplies the substitution toolkit for the multiplicative Haar measure on $(0,\infty)$ used throughout the Mellin calculus of this development, e.g. in proving the commutativity of Mellin convolution.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L64-L73

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

theorem MeasureTheory.integral_comp_inv_I0i_haar (f : ℝ → 𝕂) :
    ∫ (y : ℝ) in Ioi 0, f (1 / y) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by sorry
