-- Prove2me | Theorems.Thm_ja18_finite_stop_proof_identity_4ed333fc
-- name    : ja18_finite_stop_proof_identity_4ed333fc
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T21:26:02.706201+00:00
-- url     : https://prove2.me/theorems/22980cc2-7858-4eab-9dff-c82c9032b4f6
-- title:
--   Ja18 finite stop proof: Identity
-- statement:
--   The two expressions in the stated equality coincide under the theorem's explicit assumptions.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable section
theorem ja18_finite_stop_proof_identity_4ed333fc
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
    (hCount : (let f : ℝ≥0 → Ω → ℝ := fun t => P[J t | 𝓕.rightCont t]; (Set.range (fun ω => (τ ω : WithTop ℝ≥0))).Countable))
    (hAt : (let f : ℝ≥0 → Ω → ℝ := fun t => P[J t | 𝓕.rightCont t]; (∀ (ω : Ω), stoppedValue f (fun ω => (τ ω : WithTop ℝ≥0)) ω =
        f (τ ω) ω)))
    : (let f : ℝ≥0 → Ω → ℝ := fun t => P[J t | 𝓕.rightCont t]; ∀ᵐ ω ∂P, ∀ t ∈ F, f t ω = J t ω) := by sorry
end
