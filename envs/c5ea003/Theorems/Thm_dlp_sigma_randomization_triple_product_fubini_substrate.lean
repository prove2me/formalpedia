-- Prove2me | Theorems.Thm_dlp_sigma_randomization_triple_product_fubini_substrate
-- name    : dlp_sigma_randomization_triple_product_fubini_substrate
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-23T20:57:59.464205+00:00
-- url     : https://prove2.me/theorems/921126f5-af0d-4331-9c4c-e8bb37974eb4
-- title:
--   de la Peña–Montgomery-Smith eq. (7): triple-product Fubini substrate
-- statement:
--   de la Peña–Montgomery-Smith eq (7), order-3 (k=3) sigma-product Fubini substrate. For three independent probability sign-spaces with measures nu_1,nu_2,nu_3 and an integrable g : B1 x B2 x B3 -> E, (a) the integral of g against the product measure equals the iterated (3-fold Fubini) integral, and (b) the conditional expectation given the data coordinate equals this joint sigma-integral. This is the order-3 mirror of the eq-7 Fubini substrate the pair core 9aaf089d requires; the abstract single-product conditional-expectation step is already supplied by the order-agnostic dlp_sigma_randomization_condexp_eq_sigma_integral (786e5137, Proved), so the triple-specific content here is the 3-fold Fubini factorization of the joint sigma-integral into the iterated/product form. Closing it = MeasureTheory.integral_prod applied twice + the order-agnostic substrate 786e5137.
-- source:
--   de la Peña, Montgomery-Smith, arXiv:math/9309211, Section 4 eq (7) lines 383-396. O'Donnell, Analysis of Boolean Functions, Section 9.1.

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem dlp_sigma_randomization_triple_product_fubini_substrate
    {Ω B₁ B₂ B₃ E : Type*}
    [mΩ : MeasurableSpace Ω]
    [mB₁ : MeasurableSpace B₁] [mB₂ : MeasurableSpace B₂] [mB₃ : MeasurableSpace B₃]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) (ν₁ : Measure B₁) (ν₂ : Measure B₂) (ν₃ : Measure B₃)
    [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] [IsProbabilityMeasure ν₃]
    [SFinite ν₂] [SFinite ν₃]
    (g : B₁ × B₂ × B₃ → E)
    (hgm : StronglyMeasurable g)
    (hgi : Integrable g (ν₁.prod (ν₂.prod ν₃))) :
    (∫ b, g b ∂(ν₁.prod (ν₂.prod ν₃))
        = ∫ b₁, ∫ b₂, ∫ b₃, g (b₁, b₂, b₃) ∂ν₃ ∂ν₂ ∂ν₁)
    ∧ (μ.prod (ν₁.prod (ν₂.prod ν₃)))[
          fun ab : Ω × (B₁ × B₂ × B₃) => g ab.2 |
          MeasurableSpace.comap (Prod.fst : Ω × (B₁ × B₂ × B₃) → Ω) mΩ]
        =ᵐ[μ.prod (ν₁.prod (ν₂.prod ν₃))]
          fun _ => ∫ b, g b ∂(ν₁.prod (ν₂.prod ν₃)) := by
  sorry
