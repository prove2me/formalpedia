-- Prove2me | solution 1 for FactoringLab.cov_eq_cov_bandMean
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T02:00:26.368365+00:00
-- url     : https://prove2.me/submissions/f4bd2ca8-74ea-46c4-8c2b-3cea0e5b5265

import Mathlib
import Definitions.Def_Probability_StructuralOrthogonality
open FactoringLab Finset in
theorem solution {ι κ : Type*} [DecidableEq κ] (Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ) (g : κ → ℝ) :
    cov Ω (fun i => g (n i)) Y = cov Ω (fun i => g (n i)) (bandMean Ω n Y) := by
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
  -- `E[g(n) Y] = E[g(n) m]` and `E[Y] = E[m]`
  have h1 := key g
  have h2 : ∑ i ∈ Ω, bandMean Ω n Y i = ∑ i ∈ Ω, Y i := by simpa using key (fun _ => 1)
  simp only [cov, FactoringLab.expect]
  rw [h1, h2]
