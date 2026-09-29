-- Prove2me | solution 1 for dlp_sigma_randomization_triple_product_fubini_substrate
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-24T02:28:00.983805+00:00
-- url     : https://prove2.me/submissions/cf22a7d5-3003-4cbf-b904-bf04bcb26781

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Theorems.Thm_dlp_sigma_randomization_condexp_eq_sigma_integral

/-!
Reduction proof of `dlp_sigma_randomization_triple_product_fubini_substrate` (921126f5).

de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211) §4, eqs (4)→(7): the order-3
σ-randomization step. The order-3 (k=3) substrate is the conjunction of:

(a) a 3-fold Fubini factorization of the integral against the product measure
    `ν₁ ⊗ (ν₂ ⊗ ν₃)` into the iterated `∫∫∫` (dlP eq (7): `T_{n,3} = 2³ ∑ E(f(Z)|G₂)`
    factorizes the joint σ-integral into a product of the per-index two-point averages);
(b) the conditional-expectation-given-the-sample-block identity, which is the SAME
    order-agnostic σ-cond-exp substrate already proved at the pair level
    (`dlp_sigma_randomization_condexp_eq_sigma_integral`, node 786e5137), specialized to
    the σ-block type `B = B₁ × (B₂ × B₃)` and the σ-measure `ν = ν₁ ⊗ (ν₂ ⊗ ν₃)`.

So this is a genuine reduction onto the Proved pair substrate plus ONE extra Fubini fold
(`integral_prod` applied twice instead of once).
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem solution
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
  refine ⟨?_, ?_⟩
  · -- (a) 3-fold Fubini: integral_prod applied twice (outer ν₁ over inner ν₂.prod ν₃,
    -- then inner ν₂ over ν₃).
    rw [integral_prod _ hgi]
    refine integral_congr_ae ?_
    filter_upwards [hgi.prod_right_ae] with b₁ hb₁
    -- inner integral over ν₂.prod ν₃ : Fubini once more
    rw [integral_prod _ hb₁]
  · -- (b) reduce onto the order-agnostic σ-cond-exp substrate (pair node 786e5137),
    -- specialized to B := B₁ × (B₂ × B₃), ν := ν₁ ⊗ (ν₂ ⊗ ν₃).
    exact dlp_sigma_randomization_condexp_eq_sigma_integral
      (Ω := Ω) (B := B₁ × B₂ × B₃) (E := E)
      μ (ν₁.prod (ν₂.prod ν₃)) g hgm hgi
