-- Prove2me | Theorems.Thm_ReweightedNPMLE_hellingerSq_eq_integrals
-- name    : ReweightedNPMLE.hellingerSq_eq_integrals
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:40:56.473104+00:00
-- url     : https://prove2.me/theorems/5183cf5b-a1b1-40f4-bdf4-a099e7eb4fa6
-- title:
--   Hellinger distance as total masses minus twice the affinity
-- statement:
--   Let $p,q$ be pointwise nonnegative real functions that are integrable with respect to $\mu$, and assume $\sqrt{pq}$ is integrable. With $H^2(p,q)=\int(\sqrt p-\sqrt q)^2\,d\mu$ and affinity $A(p,q)=\int\sqrt{pq}\,d\mu$, $$H^2(p,q)=\int p\,d\mu+\int q\,d\mu-2A(p,q).$$ No unit-mass assumption is imposed. This identity links Hellinger error to likelihood-ratio expectations.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/Hellinger.lean#L420-L438

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

theorem ReweightedNPMLE.hellingerSq_eq_integrals {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpint : Integrable p μ) (hqint : Integrable q μ)
    (haint : Integrable (fun x ↦ Real.sqrt (p x * q x)) μ) :
    hellingerSq μ p q =
      (∫ x, p x ∂μ) + (∫ x, q x ∂μ) - 2 * hellingerAffinity μ p q := by sorry
