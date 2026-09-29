-- Prove2me | Theorems.Thm_entropy_convexity_refinement_marginal_le_integral_fiber
-- name    : entropy_convexity_refinement_marginal_le_integral_fiber
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-24T15:48:55.673187+00:00
-- url     : https://prove2.me/theorems/483e6b05-4c61-4cc9-b392-d9d05f41a761
-- title:
--   Convexity refinement: $\mathrm{Ent}(g_1)\le\int_y\mathrm{Ent}\,f(\cdot,y)\,d\nu$
-- statement:
--   Convexity refinement of the entropy functional (Jensen inequality for the entropy functional / log-sum inequality). For probability measures mu, nu and a positive integrable f on the product, with g1 x = the integral of f(x,.) over nu, the marginal entropy is dominated by the integral of the per-fiber entropies: Ent_mu(g1) <= integral over y of Ent_mu(f(.,y)) dnu. Combined with the general entropy chain rule this yields full two-coordinate Han subadditivity of entropy.
-- source:
--   Boucheron-Lugosi-Massart, Concentration Inequalities (OUP 2013), Theorem 4.10 (sub-additivity of entropy / two-block convexity form); Ledoux 1997; Bousquet 2002 Section 3. The pointwise log-sum inequality g1(x) log(g1(x)/M) <= integral_y f(x,y) log(f(x,y)/m_y) dnu via scalar Gibbs/Bregman with reference b(y)=g1(x) m_y/M.

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real MeasureTheory

theorem entropy_convexity_refinement_marginal_le_integral_fiber {α β : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
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
    ( (∫ x, (∫ y, f (x, y) ∂ν) * Real.log (∫ y, f (x, y) ∂ν) ∂μ)
        - (∫ x, (∫ y, f (x, y) ∂ν) ∂μ) * Real.log (∫ x, (∫ y, f (x, y) ∂ν) ∂μ) )
    ≤ ∫ y, ( (∫ x, f (x, y) * Real.log (f (x, y)) ∂μ)
              - (∫ x, f (x, y) ∂μ) * Real.log (∫ x, f (x, y) ∂μ) ) ∂ν := by
  sorry
