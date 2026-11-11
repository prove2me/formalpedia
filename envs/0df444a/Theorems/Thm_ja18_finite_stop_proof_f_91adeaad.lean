-- Prove2me | Theorems.Thm_ja18_finite_stop_proof_f_91adeaad
-- name    : ja18_finite_stop_proof_f_91adeaad
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T21:25:58.06212+00:00
-- url     : https://prove2.me/theorems/55c87098-b1e1-44c4-8bd3-9810504d0890
-- title:
--   Ja18 finite stop proof: Auxiliary result
-- statement:
--   Under the explicitly listed hypotheses, the assertion in the formal Lean theorem statement holds.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable section
theorem ja18_finite_stop_proof_f_91adeaad
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
    : (let f : ℝ≥0 → Ω → ℝ := fun t => P[J t | 𝓕.rightCont t]; Martingale f 𝓕.rightCont P) := by sorry
end
