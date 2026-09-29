-- Prove2me | Theorems.Thm_MeasureTheory_integral_comp_mul_right_I0i_haar
-- name    : MeasureTheory.integral_comp_mul_right_I0i_haar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:33:32.757031+00:00
-- url     : https://prove2.me/theorems/8a1c4d99-ba23-4bca-b330-35c6ea5a9e74
-- title:
--   Invariance of the Haar integral $\int_0^\infty f(y)\,dy/y$ under right scaling $y\mapsto ya$
-- statement:
--   Let $f\colon\mathbb{R}\to\mathbb{K}$ be a function into a normed field (the scalar field of the development), and let $a>0$. Then
--
--   $$\int_0^{\infty} f(y\,a)\,\frac{dy}{y} \;=\; \int_0^{\infty} f(y)\,\frac{dy}{y}.$$
--
--   This is the right-multiplication form of the dilation invariance of the measure $dy/y$, the Haar measure of the abelian multiplicative group $(0,\infty)$; it is of course equivalent to the left-scaling version, and both are provided for smooth rewriting in either argument order. No integrability hypothesis is needed, the equality being a measure-preserving change of variables between Bochner integrals.
--
--   It belongs to the small substitution toolkit (scaling on either side, inversion, and inversion-with-scaling) on which the Mellin calculus of this development is built — Mellin convolution identities and transform factorizations all reduce to these invariances plus Fubini.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L33-L43

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

theorem MeasureTheory.integral_comp_mul_right_I0i_haar
    (f : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
    ∫ (y : ℝ) in Ioi 0, f (y * a) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by sorry
