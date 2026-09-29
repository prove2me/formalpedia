-- Prove2me | solution 1 for PNTA.RectangleIntegral_prime_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-12T06:12:33.761164+00:00
-- url     : https://prove2.me/submissions/cce4148b-be4a-42bf-bded-d7f9577e16da

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
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs
import Theorems.Thm_PNTA_RectangleIntegral_congr

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics
open scoped Interval
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}
open PNTA

theorem solution (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral' f z w = RectangleIntegral' g z w := by
  rw [RectangleIntegral', RectangleIntegral_congr h]
