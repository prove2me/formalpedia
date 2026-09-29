-- Prove2me | solution 1 for mme_partition_mass_entropy_by_region
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T07:36:57.693181+00:00
-- url     : https://prove2.me/submissions/e8c2aad4-d5b5-43e6-90ec-3c2f40e42eec

import Theorems.Thm_mme_partition_mass_entropy_full_sum

open scoped BigOperators
open MME.RegionRate MME.RecursiveYZ

/-- A partition whose group labels retain the region has entropy equal to
the sum of its regional partition entropies. -/
theorem solution
    {R G W : Type*} [Fintype R] [Fintype G] [Fintype W]
    {C : R → Type*} [∀ r, Fintype (C r)]
    (boundary : (Σ r, C r) → Prop) [DecidablePred boundary] (group : ∀ r, C r → G)
    (mu : (Σ r, C r) → W → ℕ) :
    (∑ t, massEntropy (fun w =>
      (partCount boundary (fun c => (c.1, group c.1 c.2)) mu t w : ℝ))) =
      ∑ r, ∑ t, massEntropy (fun w =>
        (partCount (fun c : C r => boundary ⟨r, c⟩) (group r)
          (fun c w => mu ⟨r, c⟩ w) t w : ℝ)) := by
  classical
  let a : ((Σ r, C r) ⊕ (R × G)) → W → ℕ := fun t w => match t with
    | Sum.inl c => if boundary c then mu c w else 0
    | Sum.inr g => ∑ c, if ¬ boundary c ∧ (c.1, group c.1 c.2) = g then mu c w else 0
  let ar (r : R) : C r ⊕ G → W → ℕ := fun t w => match t with
    | Sum.inl c => if boundary ⟨r, c⟩ then mu ⟨r, c⟩ w else 0
    | Sum.inr g => ∑ c, if ¬ boundary ⟨r, c⟩ ∧ group r c = g then mu ⟨r, c⟩ w else 0
  have hg (r : R) (g : G) (w : W) :
      (∑ c : Σ r, C r, if ¬ boundary c ∧ (c.1, group c.1 c.2) = (r, g)
        then mu c w else 0) =
      ∑ c : C r, if ¬ boundary ⟨r, c⟩ ∧ group r c = g then mu ⟨r, c⟩ w else 0 := by
    rw [Fintype.sum_sigma, Finset.sum_eq_single r]
    · simp
    · intro r' hr' hne
      apply Finset.sum_eq_zero
      intro c hc
      simp [hne]
    · simp
  have hglobal : (∑ t, massEntropy (fun w =>
      (partCount boundary (fun c => (c.1, group c.1 c.2)) mu t w : ℝ))) =
      ∑ t, massEntropy (fun w => (a t w : ℝ)) := by
    simpa [a] using mme_partition_mass_entropy_full_sum boundary
      (fun c => (c.1, group c.1 c.2)) mu 1
  have hlocal (r : R) : (∑ t, massEntropy (fun w =>
      (partCount (fun c : C r => boundary ⟨r, c⟩) (group r)
        (fun c w => mu ⟨r, c⟩ w) t w : ℝ))) =
      ∑ t, massEntropy (fun w => (ar r t w : ℝ)) := by
    simpa [ar] using mme_partition_mass_entropy_full_sum
      (fun c : C r => boundary ⟨r, c⟩) (group r) (fun c w => mu ⟨r, c⟩ w) 1
  rw [hglobal]
  simp_rw [hlocal]
  simp only [a, ar, Fintype.sum_sum_type, Fintype.sum_sigma,
    Fintype.sum_prod_type, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro g hmem
  congr 1
  funext w
  simpa only [Fintype.sum_sigma] using congrArg (fun n : ℕ => (n : ℝ)) (hg r g w)


#print axioms solution
