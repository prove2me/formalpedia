-- Prove2me | Theorems.Thm_a06_full_history_residual_inline_measurability_46508a87
-- name    : a06_full_history_residual_inline_measurability_46508a87
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T20:26:08.830726+00:00
-- url     : https://prove2.me/theorems/2a7c1c00-ff4a-46cd-82ba-7b304083a45a
-- title:
--   A06 full history residual inline: Measurability
-- statement:
--   The specified function or random variable is measurable under the theorem's hypotheses.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat06_history_comap_prefix_representation
import Theorems.Thm_AvramDividend_Classical_chat06_prefix_observed_count_history_measurable
import Theorems.Thm_AvramDividend_Classical_chat06_arrival_prefix_reconstructs_past_count
import Theorems.Thm_AvramDividend_Classical_avram_a06_countwise_iid_residual_future_joint_ae
import Theorems.Thm_AvramDividend_Classical_avram_a06_renewal_residual_future_from_ae_threshold
import Theorems.Thm_AvramDividend_Classical_chat06_iid_shifted_suffix_common_infinite_product_law
import Theorems.Thm_AvramDividend_Classical_chat06_unit_exponential_haslaw_survival
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_residual_wait_positive_ae
import Theorems.Thm_AvramDividend_Classical_avram_a06_random_index_coordinate_measurable
import Theorems.Thm_AvramDividend_Classical_avram_a06_full_joint_factor_of_positive_tail_rectangles
open MeasureTheory Measure ProbabilityTheory Set
open scoped ENNReal

noncomputable section
theorem a06_full_history_residual_inline_measurability_46508a87
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (hExp : ∀ i, HasLaw (τ i) (expMeasure 1) P)
    (N : Ω → ℝ → ℕ)
    (hThresholdAE : ∀ᵐ ω ∂P, ∀ u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) (hclock : 0 ≤ clock)
    (hN : Measurable (fun ω => N ω clock))
    (H : Set Ω) (hH : MeasurableSet H)
    (hHpast : MeasurableSet[
      MeasurableSpace.comap
        (fun ω : Ω => fun s : Set.Iic clock => N ω (s : ℝ))
        (inferInstance : MeasurableSpace (Set.Iic clock → ℕ))] H)
    (D : Set (ℝ × (ℕ → ℝ))) (hD : MeasurableSet D) 
    (hLaw : (let μ : Measure (ℕ → ℝ) := infinitePi (fun _ : ℕ => expMeasure 1); (∀ (n : ℕ), HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω) μ P)))
    (hTail : (let μ : Measure (ℕ → ℝ) := infinitePi (fun _ : ℕ => expMeasure 1); (∀ (n : ℕ) (u : ℝ) (hu : 0 ≤ u), P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u)))))
    (hRep : (let μ : Measure (ℕ → ℝ) := infinitePi (fun _ : ℕ => expMeasure 1); (∀ (n : ℕ), ∃ Q : Set (ℕ → ℝ), MeasurableSet Q ∧
        (fun ω : Ω => ω ∈ H ∧ N ω clock = n) =ᵐ[P]
          (fun ω : Ω =>
            (fun i : ℕ => if i < n then τ i ω else 0) ∈ Q ∧
              N ω clock = n))))
    (hsum : (let μ : Measure (ℕ → ℝ) := infinitePi (fun _ : ℕ => expMeasure 1); let R : Ω → ℝ := (fun ω => τ (N ω clock) ω - (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω)); let F : Ω → (ℕ → ℝ) := fun ω j => τ (N ω clock + 1 + j) ω; Measurable (fun ω => ∑ i ∈ Finset.range (N ω clock), τ i ω)))
    (hR : (let μ : Measure (ℕ → ℝ) := infinitePi (fun _ : ℕ => expMeasure 1); let R : Ω → ℝ := (fun ω => τ (N ω clock) ω - (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω)); let F : Ω → (ℕ → ℝ) := fun ω j => τ (N ω clock + 1 + j) ω; Measurable R))
    (hF : (let μ : Measure (ℕ → ℝ) := infinitePi (fun _ : ℕ => expMeasure 1); let R : Ω → ℝ := (fun ω => τ (N ω clock) ω - (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω)); let F : Ω → (ℕ → ℝ) := fun ω j => τ (N ω clock + 1 + j) ω; Measurable F))
    (hPos : (let μ : Measure (ℕ → ℝ) := infinitePi (fun _ : ℕ => expMeasure 1); let R : Ω → ℝ := (fun ω => τ (N ω clock) ω - (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω)); let F : Ω → (ℕ → ℝ) := fun ω j => τ (N ω clock + 1 + j) ω; ∀ᵐ ω ∂P, 0 < R ω))
    : (let μ : Measure (ℕ → ℝ) := infinitePi (fun _ : ℕ => expMeasure 1); let R : Ω → ℝ := (fun ω => τ (N ω clock) ω - (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω)); let F : Ω → (ℕ → ℝ) := fun ω j => τ (N ω clock + 1 + j) ω; (∀ (u : ℝ) (hu : 0 ≤ u) (B : Set (ℕ → ℝ)) (hB : MeasurableSet B), P {ω | ω ∈ H ∧ u < R ω ∧ F ω ∈ B} =
        P H * P {ω | u < R ω ∧ F ω ∈ B})) := by sorry
end
