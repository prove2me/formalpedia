-- Prove2me | solution 1 for PNTA.ContinuousOn.rectangleBorder_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-12T05:42:36.158496+00:00
-- url     : https://prove2.me/submissions/d8b2a2e6-9c6f-40d1-afe3-dc5ca75f8fca

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
import Theorems.Thm_mapsTo_rectangleBorder_left_im
import Theorems.Thm_mapsTo_rectangleBorder_left_re
import Theorems.Thm_mapsTo_rectangleBorder_right_im
import Theorems.Thm_mapsTo_rectangleBorder_right_re

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics
open scoped Interval
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

omit [NormedSpace ℂ E] in
theorem solution (hf : ContinuousOn f (RectangleBorder z w)) :
    RectangleBorderIntegrable f z w :=
  ⟨(hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_re z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_re z w)).intervalIntegrable⟩
