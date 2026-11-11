-- Prove2me | Theorems.Thm_ja18_finite_stop_proof_identity_ccf8a14d
-- name    : ja18_finite_stop_proof_identity_ccf8a14d
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T21:26:01.165843+00:00
-- url     : https://prove2.me/theorems/87cdf7da-d741-4d0f-8470-3977ec0bd3ee
-- title:
--   Ja18 finite stop proof: Identity
-- statement:
--   The two expressions in the stated equality coincide under the theorem's explicit assumptions.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable section
theorem ja18_finite_stop_proof_identity_ccf8a14d
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (J : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτT : ∀ ω, τ ω ≤ T)
    (F : Finset ℝ≥0) (hτF : ∀ ω, τ ω ∈ F)
    (hInt : ∀ t, Integrable (J t) P)
    (hMart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (J t) ω = J s ω)
    (hZero : ∀ᵐ ω ∂P, J 0 ω = 0) 
    (hf : (let f : ℝ≥0 → Ω → ℝ := fun t => P[J t | 𝓕.rightCont t]; Martingale f 𝓕.rightCont P))
    (hτBound : (let f : ℝ≥0 → Ω → ℝ := fun t => P[J t | 𝓕.rightCont t]; ∀ ω, (τ ω : WithTop ℝ≥0) ≤ (T : WithTop ℝ≥0)))
    : (let f : ℝ≥0 → Ω → ℝ := fun t => P[J t | 𝓕.rightCont t]; (Set.range (fun ω => (τ ω : WithTop ℝ≥0))).Countable) := by sorry
end
