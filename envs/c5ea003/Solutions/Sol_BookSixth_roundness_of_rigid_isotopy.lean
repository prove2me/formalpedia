-- Prove2me | solution 1 for BookSixth.roundness_of_rigid_isotopy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-25T18:26:49.643732+00:00
-- url     : https://prove2.me/submissions/405a0cd0-e928-4a6a-995e-50da504c9e6a

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_euclidean_isometry_preserves_roundness

open scoped BigOperators
open BookSixth

/-- A family of rigid motions keeps a round circle round at every time. At each `t` the
time map is `A t • x + b t` with `A t` inner-product preserving, so the proved pointwise
theorem applies at scale `1`. The pointwise hypothesis is turned into an image equality
by `Set.image_congr'`, which is the total form and so closes in either orientation. -/
theorem solution {C : Set Space3} (hC : RoundCircle C) (G : ℝ → Space3 ≃ₜ Space3)
    (hG : ∀ t, ∃ A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ), ∃ q : ℝ × Space3,
        (∀ x y : Space3, (∑ i, (A x) i * (A y) i) = ∑ i, x i * y i) ∧
        (∀ x : Space3, (G t) x = (A x) + q.2)) :
    ∀ t, RoundCircle ((G t) '' C) := by
  intro t
  obtain ⟨A, q, hA, hmap⟩ := hG t
  have hEq : ((fun x : Space3 => (A x) + q.2) '' C) = (G t) '' C :=
    Set.image_congr' (fun x : Space3 => (hmap x).symm)
  rw [← hEq]
  have hA1 : ∀ x y : Space3, (∑ i, (A x) i * (A y) i) = ∑ i, x i * y i := hA
  have hfinal : RoundCircle ((fun x : Space3 => (1 : ℝ) • (A x) + q.2) '' C) :=
    BookSixth.euclidean_isometry_preserves_roundness C A q.2 1 hA1 (by norm_num) hC
  simpa using hfinal
