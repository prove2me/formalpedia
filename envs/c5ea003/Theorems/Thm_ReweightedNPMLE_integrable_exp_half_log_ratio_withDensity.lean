-- Prove2me | Theorems.Thm_ReweightedNPMLE_integrable_exp_half_log_ratio_withDensity
-- name    : ReweightedNPMLE.integrable_exp_half_log_ratio_withDensity
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:42:07.187181+00:00
-- url     : https://prove2.me/theorems/362771f1-5488-5565-9931-4ed6038091f4
-- title:
--   Integrability of the square-root likelihood ratio under a density change
-- statement:
--   Let $\mu$ be a measure, let $p,q:\Omega\to\mathbb R$ be strictly positive everywhere, and suppose $q$ is measurable and $\sqrt{pq}$ is integrable with respect to $\mu$. Then $$x\mapsto\exp\!\left(\tfrac12\log\frac{p(x)}{q(x)}\right)$$ is integrable with respect to the measure $q\,d\mu$. Neither density is required to have unit mass. This justifies the likelihood-ratio integral used in finite-net risk bounds.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/Hellinger.lean#L540-L558

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

theorem ReweightedNPMLE.integrable_exp_half_log_ratio_withDensity
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ)
    (hqmeas : Measurable q) (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    (haint : Integrable (fun x ↦ Real.sqrt (p x * q x)) μ) :
    Integrable (fun x ↦ Real.exp (Real.log (p x / q x) / 2))
      (μ.withDensity fun x ↦ ENNReal.ofReal (q x)) := by sorry
