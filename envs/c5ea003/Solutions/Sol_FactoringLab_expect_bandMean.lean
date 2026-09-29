-- Prove2me | solution 1 for FactoringLab.expect_bandMean
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T20:19:38.892983+00:00
-- url     : https://prove2.me/submissions/75a0c7e1-4b2c-4da4-8c5f-54451a92648f

import Mathlib
import Definitions.Def_Probability_StructuralOrthogonality

open FactoringLab
open scoped Classical

variable {ι κ : Type*} [DecidableEq κ]

private theorem sum_bandMean_eq_sum_Y (Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ) :
    ∑ i ∈ Ω, bandMean Ω n Y i = ∑ i ∈ Ω, Y i := by
  -- Partition by band label
  have hpart :
      ∑ i ∈ Ω, bandMean Ω n Y i =
        ∑ k ∈ Ω.image n, ∑ i ∈ Ω.filter (fun i => n i = k), bandMean Ω n Y i :=
    (Finset.sum_fiberwise_of_maps_to (t := Ω.image n)
      (fun i hi => Finset.mem_image_of_mem n hi) (bandMean Ω n Y)).symm
  have hpartY :
      ∑ i ∈ Ω, Y i =
        ∑ k ∈ Ω.image n, ∑ i ∈ Ω.filter (fun i => n i = k), Y i :=
    (Finset.sum_fiberwise_of_maps_to (t := Ω.image n)
      (fun i hi => Finset.mem_image_of_mem n hi) Y).symm
  rw [hpart, hpartY]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hfiber :
      ∀ i ∈ Ω.filter (fun i => n i = k),
        band Ω n i = Ω.filter (fun j => n j = k) := by
    intro i hi
    have hik : n i = k := (Finset.mem_filter.mp hi).2
    ext j
    simp only [band, Finset.mem_filter]
    constructor
    · rintro ⟨hjΩ, hji⟩
      exact ⟨hjΩ, by rw [← hik, hji]⟩
    · rintro ⟨hjΩ, hjk⟩
      exact ⟨hjΩ, by rw [hik, hjk]⟩
  have hconst :
      ∀ i ∈ Ω.filter (fun i => n i = k),
        bandMean Ω n Y i =
          (∑ j ∈ Ω.filter (fun j => n j = k), Y j) /
            ((Ω.filter (fun j => n j = k)).card : ℝ) := by
    intro i hi
    simp only [bandMean]
    rw [hfiber i hi]
  have hne : (Ω.filter (fun i => n i = k)).Nonempty := by
    rcases Finset.mem_image.mp hk with ⟨i, hiΩ, rfl⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨hiΩ, rfl⟩⟩
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Ω.filter (fun i => n i = k)).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hne).ne'
  field_simp

theorem solution (Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ) :
    FactoringLab.expect Ω (bandMean Ω n Y) = FactoringLab.expect Ω Y := by
  simp only [FactoringLab.expect, sum_bandMean_eq_sum_Y]
