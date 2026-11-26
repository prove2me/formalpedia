-- Prove2me | Theorems.Thm_ReweightedNPMLE_integral_abs_sub_le_two_mul_sqrt_hellingerSq
-- name    : ReweightedNPMLE.integral_abs_sub_le_two_mul_sqrt_hellingerSq
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:46:43.670644+00:00
-- url     : https://prove2.me/theorems/882d12ae-01fa-563e-946f-5542111bb58b
-- title:
--   Absolute density error controlled by Hellinger distance
-- statement:
--   Let $p,q$ be almost-everywhere strongly measurable, nonnegative, integrable densities with respect to a measure $\mu$, with $\int p\,d\mu=\int q\,d\mu=1$. Define $H^2(p,q)=\int(\sqrt p-\sqrt q)^2\,d\mu$, without a factor of one half. Then $$\int|p-q|\,d\mu\le2\sqrt{H^2(p,q)}.$$ This relates density estimation in Hellinger distance to $L^1$ convergence.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/Hellinger.lean#L244-L326

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

theorem ReweightedNPMLE.integral_abs_sub_le_two_mul_sqrt_hellingerSq
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ)
    (hpmeas : AEStronglyMeasurable p μ) (hqmeas : AEStronglyMeasurable q μ)
    (hp : ∀ᵐ x ∂μ, 0 ≤ p x) (hq : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hpint : Integrable p μ) (hqint : Integrable q μ)
    (hpone : ∫ x, p x ∂μ = 1) (hqone : ∫ x, q x ∂μ = 1) :
    ∫ x, |p x - q x| ∂μ ≤ 2 * Real.sqrt (hellingerSq μ p q) := by sorry
