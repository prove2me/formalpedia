-- Prove2me | solution 1 for BanditAlgorithm.l1_deviation_union_bound
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T03:56:24.018914+00:00
-- url     : https://prove2.me/submissions/248fe6df-5db2-493f-a774-5c52208fe0a7

import Theorems.Thm_BanditAlgorithm_l1_dist_eq_two_max_event_excess
import Mathlib.MeasureTheory.Measure.Real

/-!
# From an `ℓ¹` deviation to a union bound over events

The confidence sets of UCRL2 (L&S Eq. 38.13) are `ℓ¹` balls around the empirical
transition vector, and Lemma 38.8 asks for the probability that the true vector
escapes one.  The variational identity `‖p̂ - p‖₁ = 2 max_A (p̂(A) - p(A))` says
that an `ℓ¹` deviation of `ε` forces *some* event `A` to have empirical
probability exceeding its true probability by `ε/2`, and there are only `2^S`
events.  What follows is that reduction, with no probabilistic content: it turns
a uniform bound on the `2^S` scalar deviations into a bound on the `ℓ¹` one.
-/

open MeasureTheory Finset

/-- **The `ℓ¹` deviation union bound.**  If every event `A` has
`P(p̂(A) - p(A) ≥ ε/2) ≤ b`, and the two vectors always carry the same total
mass, then `P(‖p̂ - p‖₁ ≥ ε) ≤ 2^{|ι|} b`. -/
theorem solution
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (phat : Ω → ι → ℝ) (p : ι → ℝ) (ε b : ℝ)
    (hsum : ∀ ω, ∑ a, phat ω a = ∑ a, p a)
    (hbound : ∀ A : Finset ι, μ.real {ω | ε / 2 ≤ ∑ a ∈ A, (phat ω a - p a)} ≤ b) :
    μ.real {ω | ε ≤ ∑ a, |phat ω a - p a|} ≤ 2 ^ Fintype.card ι * b := by
  classical
  have hsub : {ω | ε ≤ ∑ a, |phat ω a - p a|}
      ⊆ ⋃ A : Finset ι, {ω | ε / 2 ≤ ∑ a ∈ A, (phat ω a - p a)} := by
    intro ω hω
    obtain ⟨-, A, hA⟩ := BanditAlgorithm.l1_dist_eq_two_max_event_excess (phat ω) p (hsum ω)
    refine Set.mem_iUnion.mpr ⟨A, ?_⟩
    show ε / 2 ≤ ∑ a ∈ A, (phat ω a - p a)
    have hω' : ε ≤ ∑ a, |phat ω a - p a| := hω
    rw [hA] at hω'
    linarith
  calc μ.real {ω | ε ≤ ∑ a, |phat ω a - p a|}
      ≤ μ.real (⋃ A : Finset ι, {ω | ε / 2 ≤ ∑ a ∈ A, (phat ω a - p a)}) :=
        measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ ∑ A : Finset ι, μ.real {ω | ε / 2 ≤ ∑ a ∈ A, (phat ω a - p a)} :=
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ _A : Finset ι, b := Finset.sum_le_sum fun A _ ↦ hbound A
    _ = 2 ^ Fintype.card ι * b := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul]
        push_cast
        ring
