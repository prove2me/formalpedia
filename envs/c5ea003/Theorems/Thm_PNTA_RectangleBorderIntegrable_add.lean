-- Prove2me | Theorems.Thm_PNTA_RectangleBorderIntegrable_add
-- name    : PNTA.RectangleBorderIntegrable.add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-12T05:46:08.897622+00:00
-- url     : https://prove2.me/theorems/61db3c42-a00e-4160-a150-5f6a4a0707c5
-- title:
--   Additivity of the rectangle integral for boundary-integrable functions
-- statement:
--   The rectangle contour integral is additive on integrands that are integrable along the boundary.
--
--   Say $f$ is *boundary-integrable* over the rectangle with corners $z$ and $w$ when it is interval-integrable along each of the four sides. If both $f$ and $g$ are boundary-integrable over that rectangle, then
--   $$\oint_{z}^{w} (f + g) \;=\; \oint_{z}^{w} f \;+\; \oint_{z}^{w} g .$$
--
--   The integrability hypotheses are not decorative: the contour integral is a combination of four interval integrals, and splitting the integral of a sum into a sum of integrals requires each piece to converge. This lemma is what licenses decomposing an integrand into a main term and an error term and integrating each separately.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean#L210-L221

/-
Extracted from PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
commit f55e85551ac10e96d98262a354cfcaac2825f2da, Apache 2.0 license.
Wrapped in namespace PNTA for the Prove2Me platform.
-/

import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Definitions.Def_ResidueCalcOnRectangles_defs

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics
open scoped Interval
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

theorem PNTA.RectangleBorderIntegrable.add {f g : ℂ → E}
    (hf : RectangleBorderIntegrable f z w) (hg : RectangleBorderIntegrable g z w) :
    RectangleIntegral (f + g) z w = RectangleIntegral f z w + RectangleIntegral g z w := by sorry
