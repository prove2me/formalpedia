-- Prove2me | solution 1 for BookSixth.euclidean_isometry_preserves_roundness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-25T18:06:28.856988+00:00
-- url     : https://prove2.me/submissions/c208f03b-4c88-467d-b34f-aa6c445a3048

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

/-- A Euclidean isometry of `Space3`, followed by a positive scaling and a translation,
sends a round circle to a round circle.

The witness is `a • A c + b`, `A u`, `A v`, `a * r`.

Note on the hypothesis: `Space3 = Fin 3 → ℝ` carries the **sup** norm, not the Euclidean
one, so `∀ x, ‖A x‖ = ‖x‖` does NOT say that `A` preserves lengths and cannot be used to
prove this. The hypothesis is therefore stated as preservation of the Euclidean bilinear
form `β x y = ∑ i, x i * y i` directly, which is exactly orthogonality on `ℝ³` (and
implies length preservation by the polarization identity). -/
theorem solution (C : Set Space3) (A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) (b : Space3)
    (a : ℝ) (hA : ∀ x y : Space3, (∑ i, (A x) i * (A y) i) = ∑ i, x i * y i)
    (ha : 0 < a) (hC : RoundCircle C) :
    RoundCircle ((fun x : Space3 => a • (A x) + b) '' C) := by
  obtain ⟨c, u, v, r, hr, hu, hv, huv, hCeq⟩ := hC
  refine ⟨a • (A c) + b, A u, A v, a * r, mul_pos ha hr,
    hA u u |>.trans hu, hA v v |>.trans hv, hA u v |>.trans huv, ?_⟩
  rw [hCeq, ← Set.range_comp']
  congr 1
  funext t
  funext i
  fin_cases i <;>
    simp [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_add, smul_smul] <;>
    ring
