-- Prove2me | Theorems.Thm_entropy_full_two_coordinate_han_subadditivity
-- name    : entropy_full_two_coordinate_han_subadditivity
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-24T15:52:55.208509+00:00
-- url     : https://prove2.me/theorems/922645de-b0c5-4017-bfdc-3ca2b0301e8a
-- title:
--   Full two-coordinate Han subadditivity of the entropy functional
-- statement:
--   Full two-coordinate Han subadditivity of the entropy functional. For probability measures mu, nu and positive integrable f on the product, Ent_{mu tensor nu}(f) <= integral_y Ent_mu(f(.,y)) dnu + integral_x Ent_nu(f(x,.)) dmu, where Ent_m(h) = integral h log h dm - (integral h dm) log(integral h dm). Obtained by combining the exact entropy chain rule with the convexity refinement.
-- source:
--   Boucheron-Lugosi-Massart, Concentration Inequalities (OUP 2013), Theorem 4.10 (sub-additivity / tensorization of entropy); Ledoux 1997; Bousquet 2002 Section 3. Reduction onto the chain rule (entropy_chain_rule_general_two_coordinate_han_subadditivity) and the convexity refinement (entropy_convexity_refinement_marginal_le_integral_fiber).

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real MeasureTheory

theorem entropy_full_two_coordinate_han_subadditivity {α β : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : α × β → ℝ}
    (hf_pos : ∀ p, 0 < f p)
    (hf_int : Integrable f (μ.prod ν))
    (hflog_int : Integrable (fun p ↦ f p * Real.log (f p)) (μ.prod ν))
    (hg1log_int : Integrable (fun x ↦ (∫ y, f (x, y) ∂ν) * Real.log (∫ y, f (x, y) ∂ν)) μ)
    (hm_int : Integrable (fun y ↦ ∫ x, f (x, y) ∂μ) ν)
    (hfx_int : ∀ x, Integrable (fun y ↦ f (x, y)) ν)
    (hfx_logm_int : ∀ x, Integrable (fun y ↦ f (x, y) * Real.log (∫ x', f (x', y) ∂μ)) ν)
    (hfx_logf_int : ∀ x, Integrable (fun y ↦ f (x, y) * Real.log (f (x, y))) ν)
    (h_inner_x_int :
      Integrable (fun x ↦ ∫ y, (f (x, y) * Real.log (f (x, y))
        - f (x, y) * Real.log (∫ x', f (x', y) ∂μ)) ∂ν) μ)
    (hfm_prod_int :
      Integrable (fun p : α × β ↦ f p * Real.log (∫ x', f (x', p.2) ∂μ)) (μ.prod ν)) :
    ((∫ p, f p * Real.log (f p) ∂(μ.prod ν))
        - (∫ p, f p ∂(μ.prod ν)) * Real.log (∫ p, f p ∂(μ.prod ν)))
      ≤ (∫ y, ((∫ x, f (x, y) * Real.log (f (x, y)) ∂μ)
            - (∫ x, f (x, y) ∂μ) * Real.log (∫ x, f (x, y) ∂μ)) ∂ν)
        + ∫ x, ((∫ y, f (x, y) * Real.log (f (x, y)) ∂ν)
            - (∫ y, f (x, y) ∂ν) * Real.log (∫ y, f (x, y) ∂ν)) ∂μ := by
  sorry
