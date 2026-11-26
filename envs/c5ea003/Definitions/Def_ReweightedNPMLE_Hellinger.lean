-- Prove2me | Definitions.Def_ReweightedNPMLE_Hellinger
-- name    : ReweightedNPMLE_Hellinger
-- status  : Definition
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:15:32.411077+00:00
-- url     : https://prove2.me/theorems/32db0771-4c24-4d82-af94-1bb13c72044b
-- title:
--   Squared Hellinger distance and Hellinger affinity
-- statement:
--   For a measure \(\mu\) on a measurable space and real-valued functions \(p,q\), define
--   \[
--   H_\mu^2(p,q)=\int(\sqrt{p(x)}-\sqrt{q(x)})^2\,d\mu(x),\qquad
--   \mathcal A_\mu(p,q)=\int\sqrt{p(x)q(x)}\,d\mu(x).
--   \]
--   For probability densities, \(H_\mu^2\) is the squared Hellinger distance under the convention with no factor \(1/2\), and \(\mathcal A_\mu\) is the Hellinger affinity. The definitions use real square roots, which take value zero on negative arguments; the probability-density interpretation uses nonnegative, normalized densities.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/Hellinger.lean#L22-L30

import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-!
# Squared Hellinger distance

This file formalizes the normalization convention used in the manuscript,
`H²(p,q) = ∫ (√p-√q)²`, and its affinity identity.
-/

open MeasureTheory Filter Topology

namespace ReweightedNPMLE

/-- Squared Hellinger distance with respect to a dominating measure. -/
noncomputable def hellingerSq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ) : ℝ :=
  ∫ x, (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ∂μ

/-- Hellinger affinity `∫ √(pq)`. -/
noncomputable def hellingerAffinity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ) : ℝ :=
  ∫ x, Real.sqrt (p x * q x) ∂μ





















































end ReweightedNPMLE


