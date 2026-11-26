-- Prove2me | Theorems.Thm_ReweightedNPMLE_sqrt_sub_sq_le_abs_sub
-- name    : ReweightedNPMLE.sqrt_sub_sq_le_abs_sub
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:40:50.549811+00:00
-- url     : https://prove2.me/theorems/7bbe7bc1-3928-4bc1-a681-db145202e90e
-- title:
--   Pointwise Hellinger error is bounded by absolute density error
-- statement:
--   For nonnegative real numbers $a,b$, $$(\sqrt a-\sqrt b)^2\le|a-b|.$$ This elementary inequality converts an $L^1$ approximation of nonnegative functions into a bound for their squared Hellinger distance.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/Hellinger.lean#L37-L59

import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Hellinger

/-!
# Squared Hellinger distance

This file formalizes the normalization convention used in the manuscript,
`H²(p,q) = ∫ (√p-√q)²`, and its affinity identity.
-/

open MeasureTheory Filter Topology

open ReweightedNPMLE

theorem ReweightedNPMLE.sqrt_sub_sq_le_abs_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ |a - b| := by sorry
