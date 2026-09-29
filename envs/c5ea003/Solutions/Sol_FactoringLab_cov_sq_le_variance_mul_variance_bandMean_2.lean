-- Prove2me | solution 2 for FactoringLab.cov_sq_le_variance_mul_variance_bandMean
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T01:48:31.208719+00:00
-- url     : https://prove2.me/submissions/4476789f-913e-44b3-b43d-83c13b242fe1

import Mathlib
import Definitions.Def_Probability_StructuralOrthogonality
open FactoringLab Finset in
theorem solution {ι κ : Type*} [DecidableEq κ] (Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ)
    (g : κ → ℝ) :
    (cov Ω (fun i => g (n i)) Y) ^ 2
      ≤ variance Ω (fun i => g (n i)) * variance Ω (bandMean Ω n Y) := by
  have key : ∀ g : κ → ℝ,
      ∑ i ∈ Ω, g (n i) * bandMean Ω n Y i = ∑ i ∈ Ω, g (n i) * Y i := by
    intro g
    have hmap : ∀ i ∈ Ω, n i ∈ Ω.image n := fun i hi => mem_image_of_mem n hi
    rw [← sum_fiberwise_of_maps_to hmap, ← sum_fiberwise_of_maps_to hmap]
    refine sum_congr rfl fun k hk => ?_
    have hband : ∀ i ∈ Ω.filter (fun i => n i = k), band Ω n i = Ω.filter (fun j => n j = k) := by
      intro i hi
      rw [mem_filter] at hi
      unfold band
      rw [hi.2]
    have hlhs : ∑ i ∈ Ω.filter (fun i => n i = k), g (n i) * bandMean Ω n Y i
        = ∑ _i ∈ Ω.filter (fun i => n i = k),
            g k * ((∑ j ∈ Ω.filter (fun j => n j = k), Y j) / (Ω.filter (fun j => n j = k)).card) := by
      refine sum_congr rfl fun i hi => ?_
      rw [bandMean, hband i hi, (mem_filter.mp hi).2]
    have hrhs : ∑ i ∈ Ω.filter (fun i => n i = k), g (n i) * Y i
        = ∑ i ∈ Ω.filter (fun i => n i = k), g k * Y i := by
      refine sum_congr rfl fun i hi => ?_
      rw [(mem_filter.mp hi).2]
    rw [hlhs, hrhs, sum_const, nsmul_eq_mul, ← mul_sum]
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hk
    have hne : ((Ω.filter (fun j => n j = n i)).card : ℝ) ≠ 0 := by
      have : 0 < (Ω.filter (fun j => n j = n i)).card :=
        card_pos.mpr ⟨i, mem_filter.mpr ⟨hi, rfl⟩⟩
      exact_mod_cast this.ne'
    field_simp
  -- centred form of the covariance
  have hcen : ∀ U V : ι → ℝ, cov Ω U V
      = (∑ i ∈ Ω, (U i - FactoringLab.expect Ω U) * (V i - FactoringLab.expect Ω V)) / Ω.card := by
    intro U V
    by_cases hΩ : Ω.card = 0
    · have h0 : Ω = ∅ := card_eq_zero.mp hΩ
      subst h0
      simp [cov, FactoringLab.expect]
    · have hN : (Ω.card : ℝ) ≠ 0 := by exact_mod_cast hΩ
      simp only [cov, FactoringLab.expect]
      have e : ∀ i, (U i - (∑ j ∈ Ω, U j) / Ω.card) * (V i - (∑ j ∈ Ω, V j) / Ω.card)
          = U i * V i - U i * ((∑ j ∈ Ω, V j) / Ω.card) - (∑ j ∈ Ω, U j) / Ω.card * V i
            + (∑ j ∈ Ω, U j) / Ω.card * ((∑ j ∈ Ω, V j) / Ω.card) := fun i => by ring
      rw [sum_congr rfl (fun i _ => e i), sum_add_distrib, sum_sub_distrib, sum_sub_distrib,
        ← sum_mul, ← mul_sum, sum_const, nsmul_eq_mul]
      field_simp
      ring
  -- Cauchy–Schwarz for the covariance
  have hcs : ∀ U V : ι → ℝ, (cov Ω U V) ^ 2 ≤ variance Ω U * variance Ω V := by
    intro U V
    have hsq := sum_mul_sq_le_sq_mul_sq Ω (fun i => U i - FactoringLab.expect Ω U)
      (fun i => V i - FactoringLab.expect Ω V)
    have hUU : ∑ i ∈ Ω, (U i - FactoringLab.expect Ω U) * (U i - FactoringLab.expect Ω U)
        = ∑ i ∈ Ω, (U i - FactoringLab.expect Ω U) ^ 2 := sum_congr rfl (fun i _ => by ring)
    have hVV : ∑ i ∈ Ω, (V i - FactoringLab.expect Ω V) * (V i - FactoringLab.expect Ω V)
        = ∑ i ∈ Ω, (V i - FactoringLab.expect Ω V) ^ 2 := sum_congr rfl (fun i _ => by ring)
    rw [variance, variance, hcen, hcen, hcen, hUU, hVV, div_pow, div_mul_div_comm, ← sq]
    exact div_le_div_of_nonneg_right hsq (sq_nonneg _)
  -- `cov(g(n), Y) = cov(g(n), E[Y | n])`
  have hcov : cov Ω (fun i => g (n i)) Y = cov Ω (fun i => g (n i)) (bandMean Ω n Y) := by
    have h1 := key g
    have h2 : ∑ i ∈ Ω, bandMean Ω n Y i = ∑ i ∈ Ω, Y i := by simpa using key (fun _ => 1)
    simp only [cov, FactoringLab.expect]
    rw [h1, h2]
  rw [hcov]
  exact hcs _ _
