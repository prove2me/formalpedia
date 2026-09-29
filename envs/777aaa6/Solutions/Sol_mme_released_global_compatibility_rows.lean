-- Prove2me | solution 1 for mme_released_global_compatibility_rows
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:13:18.037465+00:00
-- url     : https://prove2.me/submissions/62f4009e-133c-48bc-b321-a1d6238ce5eb

import Definitions.Def_mme_released_global_profile_data

open scoped BigOperators Classical
open MME MME.RegionRate MME.ReleasedGlobal MME.RecursiveYZ

/-- Rational rows matched to the actual boundary and pooled interior masses
compute the complete outer compatibility potential. -/
theorem solution
    (owner : Fin 6) (i : Fin 2) (x : (Fin 45 ⊕ Fin 9) → Word → ℚ)
    (hb : ∀ s w, (x (Sum.inl s) w : ℝ) =
      if yzBoundary (half := 8) (parent := fun (_ : Fin 1) (_ : Fin 3) ↦ 8) i ⟨0, shapeEquiv s⟩ then
        (profile owner).2 (yzMode i) ⟨0, shapeEquiv s⟩ w else 0)
    (hi : ∀ j w, (x (Sum.inr j) w : ℝ) =
      ∑ c : Shape, if ¬ yzBoundary (half := 8) (parent := fun (_ : Fin 1) (_ : Fin 3) ↦ 8) i ⟨0, c⟩ ∧ c.val (yzMode i) = j then
        (profile owner).2 (yzMode i) ⟨0, c⟩ w else 0) :
    (profile owner).compat i 0 =
      ∑ a, massEntropy (fun w ↦ (x a w : ℝ)) := by
  simp only [GlobalCW.EntropyProfile.compat, Fintype.sum_sum_type]
  congr 1
  · rw [← Finset.sum_subtype (Finset.univ.filter (fun c : Shape ↦ yzBoundary (half := 8) (parent := fun (_ : Fin 1) (_ : Fin 3) ↦ 8) i ⟨0, c⟩))
      (fun c => by simp) (fun c ↦ massEntropy (fun w ↦ (profile owner).2 (yzMode i) ⟨0, c⟩ w)),
      Finset.sum_filter, ← shapeEquiv.sum_comp]
    apply Finset.sum_congr rfl
    intro s hs
    simp_rw [hb]
    by_cases hc : yzBoundary (half := 8) (parent := fun (_ : Fin 1) (_ : Fin 3) ↦ 8) i ⟨0, shapeEquiv s⟩ <;> simp [hc, massEntropy, entropy]
  · apply Finset.sum_congr rfl
    intro j hj
    simp_rw [hi]


#print axioms solution
