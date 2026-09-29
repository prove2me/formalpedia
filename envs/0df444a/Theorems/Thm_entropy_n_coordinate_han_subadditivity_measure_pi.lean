-- Prove2me | Theorems.Thm_entropy_n_coordinate_han_subadditivity_measure_pi
-- name    : entropy_n_coordinate_han_subadditivity_measure_pi
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-24T16:23:23.093749+00:00
-- url     : https://prove2.me/theorems/ab595257-77bb-474b-8e78-90f4ac4b54b2
-- title:
--   BLM Theorem 4.10: $n$-coordinate Han subadditivity over a product measure
-- statement:
--   n-coordinate Han subadditivity (tensorization) of the entropy functional over a product measure Measure.pi mu on Fin n. Given the two-coordinate Han inequality H2 and a measurable g with 0 < c <= g <= C, the entropy of g under P = Measure.pi mu is bounded by the sum over coordinates k of the conditional entropy of coordinate k integrated over the others: Ent_P(g) <= sum_k [ integral g log g dP - integral (integral_t g(update x k t) dmu_k) log(...) dP ], the k-th summand written purely with Function.update and P. Ent_m(h) = integral h log h dm - (integral h dm) log(integral h dm), written inline.
-- source:
--   Boucheron-Lugosi-Massart, Concentration Inequalities (OUP 2013), Theorem 4.10 (sub-additivity / tensorization of entropy = Han's inequality); Ledoux 1997; Bousquet 2002 Section 3. Proof = induction on n, peeling coordinate 0 via MeasurableEquiv.piFinSuccAbove (measurePreserving_piFinSuccAbove) and applying the two-coordinate Han inequality, then re-indexing the summands; bounded-positive g discharges integrability.

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Constructions.Pi

open Real MeasureTheory

theorem entropy_n_coordinate_han_subadditivity_measure_pi (H2 : ∀ {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
      (ρ : Measure A) (σ : Measure B) [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ]
      (F : A × B → ℝ),
      ((∫ p, F p * Real.log (F p) ∂(ρ.prod σ))
          - (∫ p, F p ∂(ρ.prod σ)) * Real.log (∫ p, F p ∂(ρ.prod σ)))
        ≤ (∫ y, ((∫ x, F (x, y) * Real.log (F (x, y)) ∂ρ)
              - (∫ x, F (x, y) ∂ρ) * Real.log (∫ x, F (x, y) ∂ρ)) ∂σ)
          + ∫ x, ((∫ y, F (x, y) * Real.log (F (x, y)) ∂σ)
              - (∫ y, F (x, y) ∂σ) * Real.log (∫ y, F (x, y) ∂σ)) ∂ρ)
    {n : ℕ} {α : Fin n → Type} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    {g : (∀ i, α i) → ℝ} {c C : ℝ}
    (hmeas : Measurable g) (hcpos : 0 < c) (hlb : ∀ x, c ≤ g x) (hub : ∀ x, g x ≤ C) :
    ((∫ x, g x * Real.log (g x) ∂(Measure.pi μ))
        - (∫ x, g x ∂(Measure.pi μ)) * Real.log (∫ x, g x ∂(Measure.pi μ)))
      ≤ ∑ k : Fin n,
          ((∫ x, g x * Real.log (g x) ∂(Measure.pi μ))
            - ∫ x, (∫ t, g (Function.update x k t) ∂(μ k))
                * Real.log (∫ t, g (Function.update x k t) ∂(μ k)) ∂(Measure.pi μ)) := by
  sorry
