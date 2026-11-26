-- Prove2me | Theorems.Thm_ReweightedNPMLE_density_mul_exp_half_log_ratio
-- name    : ReweightedNPMLE.density_mul_exp_half_log_ratio
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:41:42.357014+00:00
-- url     : https://prove2.me/theorems/3457ca0e-351e-47fa-be5c-ee1e0232fdec
-- title:
--   Change-of-density identity for the square-root likelihood ratio
-- statement:
--   For strictly positive real numbers $p,q$, $$q\exp\!\left(\tfrac12\log(p/q)\right)=\sqrt{pq}.$$ Integrating this identity with a reference density turns the square-root likelihood-ratio moment into Hellinger affinity.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/Hellinger.lean#L479-L492

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

theorem ReweightedNPMLE.density_mul_exp_half_log_ratio {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    q * Real.exp (Real.log (p / q) / 2) = Real.sqrt (p * q) := by sorry
