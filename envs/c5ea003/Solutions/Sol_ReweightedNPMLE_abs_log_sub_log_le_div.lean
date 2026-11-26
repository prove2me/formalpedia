-- Prove2me | solution 1 for ReweightedNPMLE.abs_log_sub_log_le_div
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:52:42.606833+00:00
-- url     : https://prove2.me/submissions/69e7d639-31c6-4b73-bea3-82eb7b45d2a6

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Regularity of the fitted-value problem

This file proves the analytic regularity part of the paper's effective-dimension
argument.  Variational inequalities yield a quantitative local Lipschitz bound
for the unique fitted vector and its coordinatewise logarithm.  Mathlib's
Rademacher theorem then gives almost-everywhere differentiability.
-/

open Set MeasureTheory Filter
open scoped BigOperators NNReal

open ReweightedNPMLE
open ReweightedNPMLE in
/-- The logarithm is `c⁻¹`-Lipschitz on `[c,∞)`. -/
theorem solution {c x y : ℝ}
    (hc : 0 < c) (hx : c ≤ x) (hy : c ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / c := by
  have hxpos : 0 < x := hc.trans_le hx
  have hypos : 0 < y := hc.trans_le hy
  rcases le_total x y with hxy | hyx
  · have hlog : Real.log y - Real.log x ≤ y / x - 1 := by
      rw [← Real.log_div hypos.ne' hxpos.ne']
      exact Real.log_le_sub_one_of_pos (div_pos hypos hxpos)
    have hfrac : y / x - 1 ≤ (y - x) / c := by
      rw [show y / x - 1 = (y - x) / x by field_simp [hxpos.ne']]
      exact div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) hc hx
    calc
      |Real.log x - Real.log y| = Real.log y - Real.log x := by
        rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hxpos hxy))]
        ring
      _ ≤ y / x - 1 := hlog
      _ ≤ (y - x) / c := hfrac
      _ = |x - y| / c := by rw [abs_of_nonpos (sub_nonpos.mpr hxy)]; ring
  · have hlog : Real.log x - Real.log y ≤ x / y - 1 := by
      rw [← Real.log_div hxpos.ne' hypos.ne']
      exact Real.log_le_sub_one_of_pos (div_pos hxpos hypos)
    have hfrac : x / y - 1 ≤ (x - y) / c := by
      rw [show x / y - 1 = (x - y) / y by field_simp [hypos.ne']]
      exact div_le_div_of_nonneg_left (sub_nonneg.mpr hyx) hc hy
    calc
      |Real.log x - Real.log y| = Real.log x - Real.log y := by
        rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hypos hyx))]
      _ ≤ x / y - 1 := hlog
      _ ≤ (x - y) / c := hfrac
      _ = |x - y| / c := by rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
