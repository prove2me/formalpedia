-- Prove2me | solution 1 for BookSixth.roundness_of_rigid_similarity_isotopy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-25T18:43:51.352104+00:00
-- url     : https://prove2.me/submissions/9337aa37-bdca-4bf7-adb5-b15eaeea90ae

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_euclidean_isometry_preserves_roundness

open scoped BigOperators
open BookSixth

/-- A family of scaled orthogonal maps keeps a round circle round at every time.

This is the time-indexed form of the pointwise lemma
`euclidean_isometry_preserves_roundness`: at each time the hypothesis is unpacked and
the pointwise result is applied, and the hypothesis is turned into the needed image
equality by `Set.image_congr'`. -/
theorem solution {C : Set Space3} (hC : RoundCircle C) (G : ℝ → Space3 ≃ₜ Space3)
    (hG : ∀ t, ∃ A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ), ∃ a : ℝ, ∃ b : Space3, 0 < a ∧
        (∀ x y : Space3, (∑ i, (A x) i * (A y) i) = ∑ i, x i * y i) ∧
        (∀ x : Space3, (G t) x = a • (A x) + b)) :
    ∀ t, RoundCircle ((G t) '' C) := by
  intro t
  obtain ⟨A, a, b, ha, hA, hmap⟩ := hG t
  have hEq : ((fun x : Space3 => a • (A x) + b) '' C) = (G t) '' C :=
    Set.image_congr' (fun x : Space3 => (hmap x).symm)
  rw [← hEq]
  exact BookSixth.euclidean_isometry_preserves_roundness C A b a hA ha hC
