-- Prove2me | solution 1 for entropy_chain_rule_general_two_coordinate_han_subadditivity
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-24T15:27:38.128865+00:00
-- url     : https://prove2.me/submissions/2bb8b347-cf29-4a02-9b4b-87b42691a1c6

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real MeasureTheory

/-- **Entropy chain rule (general two-coordinate Han subadditivity, exact form).**

BLM *Concentration Inequalities* Thm 4.10 / Ledoux 1997 / Bousquet 2002 §3 (tensorization
of entropy), the GENERAL (non-product) function case.  For probability measures `μ, ν`,
a nonnegative `f : α × β → ℝ` with `f` and `f·log f` integrable for `μ.prod ν` and the
second-coordinate marginal `g₁ x = ∫ f(x,·) dν` having integrable `g₁·log g₁`, the entropy
functional `Ent_m(g) = ∫ g log g dm − (∫ g)·log(∫ g)` satisfies the exact chain rule

  `Ent_{μ⊗ν}(f) = Ent_μ(g₁) + ∫_x Ent_ν(f(x,·)) dμ.`

(`Ent` written inline.)  Proof = pure Fubini + linearity: the marginal-entropy term
`∫ g₁ log g₁` inside `∫_x Ent_ν(f(x,·))` cancels with the same term inside `Ent_μ(g₁)`. -/
theorem solution
    {α β : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : α × β → ℝ}
    (hf_int : Integrable f (μ.prod ν))
    (hflog_int : Integrable (fun p ↦ f p * Real.log (f p)) (μ.prod ν))
    (hg1log_int : Integrable (fun x ↦ (∫ y, f (x, y) ∂ν) * Real.log (∫ y, f (x, y) ∂ν)) μ) :
    ((∫ p, f p * Real.log (f p) ∂(μ.prod ν))
        - (∫ p, f p ∂(μ.prod ν)) * Real.log (∫ p, f p ∂(μ.prod ν)))
      = ((∫ x, (∫ y, f (x, y) ∂ν) * Real.log (∫ y, f (x, y) ∂ν) ∂μ)
          - (∫ x, (∫ y, f (x, y) ∂ν) ∂μ) * Real.log (∫ x, (∫ y, f (x, y) ∂ν) ∂μ))
        + ∫ x, ((∫ y, f (x, y) * Real.log (f (x, y)) ∂ν)
            - (∫ y, f (x, y) ∂ν) * Real.log (∫ y, f (x, y) ∂ν)) ∂μ := by
  classical
  set g₁ : α → ℝ := fun x ↦ ∫ y, f (x, y) ∂ν with hg₁
  set m : ℝ := ∫ p, f p ∂(μ.prod ν) with hm
  have hmass : (∫ x, g₁ x ∂μ) = m := by
    rw [hg₁, hm, ← integral_prod f hf_int]
  have hflogfubini :
      (∫ p, f p * Real.log (f p) ∂(μ.prod ν))
        = ∫ x, (∫ y, f (x, y) * Real.log (f (x, y)) ∂ν) ∂μ := by
    rw [← integral_prod _ hflog_int]
  have hcondlog_int : Integrable (fun x ↦ ∫ y, f (x, y) * Real.log (f (x, y)) ∂ν) μ := by
    have := hflog_int.integral_prod_left
    simpa using this
  have hint_cond :
      (∫ x, ((∫ y, f (x, y) * Real.log (f (x, y)) ∂ν) - g₁ x * Real.log (g₁ x)) ∂μ)
        = (∫ x, (∫ y, f (x, y) * Real.log (f (x, y)) ∂ν) ∂μ)
          - ∫ x, g₁ x * Real.log (g₁ x) ∂μ :=
    integral_sub hcondlog_int hg1log_int
  rw [hint_cond, hmass, hflogfubini]
  ring
