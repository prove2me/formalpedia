-- Prove2me | Theorems.Thm_PNTA_RectangleIntegral_translate
-- name    : PNTA.RectangleIntegral.translate
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-12T05:48:06.669862+00:00
-- url     : https://prove2.me/theorems/6705b253-c53f-4e41-a3fe-1b80dec0a200
-- title:
--   Translating the integrand translates the rectangle
-- statement:
--   Shifting the argument of the integrand is the same as shifting the contour.
--
--   For any $f : \mathbb{C} \to E$, corners $z, w$, and shift $p \in \mathbb{C}$,
--   $$\oint_{z}^{w} f(s - p)\,ds \;=\; \oint_{z - p}^{w - p} f(s)\,ds .$$
--
--   This is the change of variables $s \mapsto s + p$ for rectangle contours, and it is what reduces a residue computation at an arbitrary point $p$ to the corresponding computation at the origin — the standard normalisation step before applying the residue theorem.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean#L476-L481

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

theorem PNTA.RectangleIntegral.translate (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral (fun s => f (s - p)) z w = RectangleIntegral f (z - p) (w - p) := by sorry
