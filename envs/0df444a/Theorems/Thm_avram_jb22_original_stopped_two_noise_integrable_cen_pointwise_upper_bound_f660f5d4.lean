-- Prove2me | Theorems.Thm_avram_jb22_original_stopped_two_noise_integrable_cen_pointwise_upper_bound_f660f5d4
-- name    : avram_jb22_original_stopped_two_noise_integrable_cen_pointwise_upper_bound_f660f5d4
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:34:36.860467+00:00
-- url     : https://prove2.me/theorems/6e181a5f-5aef-4fbb-a8d8-89ebf0c5f333
-- title:
--   Avram jb22 original stopped two noise integrable centered limits: Pointwise upper bound
-- statement:
--   At every point covered by the stated hypotheses, the left-hand expression is at most the right-hand expression.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jb22_original_stopped_two_noise_dominated_mesh_limit
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

noncomputable section
theorem avram_jb22_original_stopped_two_noise_integrable_cen_pointwise_upper_bound_f660f5d4
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {ι : Type*} (S : ℕ → Finset ι)
    (R J : ℝ≥0 → Ω → ℝ)
    (hRint : ∀ u : ℝ≥0, Integrable (R u) P)
    (hRmart : ∀ u v : ℝ≥0, u ≤ v →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont u) P (R v) ω = R u ω)
    (hJint : ∀ u : ℝ≥0, Integrable (J u) P)
    (hJmart : ∀ u v : ℝ≥0, u ≤ v →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont u) P (J v) ω = J u ω)
    (a b : ℕ → ι → ℝ≥0)
    (WG WJ : ℕ → ι → Ω → ℝ)
    (hab : ∀ k, ∀ i ∈ S k, a k i ≤ b k i)
    (hWG : ∀ k, ∀ i ∈ S k,
      Measurable[𝓕.rightCont (a k i)] (WG k i))
    (hWJ : ∀ k, ∀ i ∈ S k,
      Measurable[𝓕.rightCont (a k i)] (WJ k i))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hGprod : ∀ k, ∀ i ∈ S k,
      Integrable (fun ω =>
        (if τ ω ≤ a k i then 0 else WG k i ω) *
          (R (b k i) ω - R (a k i) ω)) P)
    (hJprod : ∀ k, ∀ i ∈ S k,
      Integrable (fun ω =>
        (if τ ω ≤ a k i then 0 else WJ k i ω) *
          (J (b k i) ω - J (a k i) ω)) P)
    (Gseq Jseq : ℕ → Ω → ℝ)
    (hGsource : ∀ k ω, Gseq k ω =
      ∑ i ∈ S k, (if τ ω ≤ a k i then 0 else WG k i ω) *
        (R (b k i) ω - R (a k i) ω))
    (hJsource : ∀ k ω, Jseq k ω =
      ∑ i ∈ S k, (if τ ω ≤ a k i then 0 else WJ k i ω) *
        (J (b k i) ω - J (a k i) ω))
    (MG MJ BG BJ : Ω → ℝ)
    (hGconv : ∀ᵐ ω ∂P,
      Tendsto (fun k => Gseq k ω) atTop (𝓝 (MG ω)))
    (hJconv : ∀ᵐ ω ∂P,
      Tendsto (fun k => Jseq k ω) atTop (𝓝 (MJ ω)))
    (hBG : Integrable BG P) (hBJ : Integrable BJ P)
    (hGdom : ∀ k, ∀ᵐ ω ∂P, ‖Gseq k ω‖ ≤ BG ω)
    (hJdom : ∀ k, ∀ᵐ ω ∂P, ‖Jseq k ω‖ ≤ BJ ω)
    (hMGAE : AEStronglyMeasurable MG P)
    (hMJAE : AEStronglyMeasurable MJ P) 
    (hGdomall : ∀ᵐ ω ∂P, ∀ k, ‖Gseq k ω‖ ≤ BG ω)
    (hJdomall : ∀ᵐ ω ∂P, ∀ k, ‖Jseq k ω‖ ≤ BJ ω)
    (hGbound : ∀ᵐ ω ∂P, ‖MG ω‖ ≤ ‖BG ω‖)
    : ∀ᵐ ω ∂P, ‖MJ ω‖ ≤ ‖BJ ω‖ := by sorry
end
