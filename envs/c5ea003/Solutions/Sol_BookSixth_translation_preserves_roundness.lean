-- Prove2me | solution 1 for BookSixth.translation_preserves_roundness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-25T17:11:05.429553+00:00
-- url     : https://prove2.me/submissions/c9a63b88-0e0d-4d56-97f7-e776b56e8c47

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

/-- Translation sends a round circle to a round circle. The orthonormal frame `u`, `v`
is unchanged and only the centre moves from `c` to `c + b`, so the three orthonormal
equations are inherited verbatim. -/
theorem solution (C : Set Space3) (b : Space3) (hC : RoundCircle C) :
    RoundCircle ((fun x : Space3 => x + b) '' C) := by
  obtain ⟨c, u, v, r, hr, hu, hv, huv, hCeq⟩ := hC
  refine ⟨c + b, u, v, r, hr, hu, hv, huv, ?_⟩
  rw [hCeq, ← Set.range_comp']
  congr 1
  funext t
  funext i
  fin_cases i <;>
    simp [map_add, Pi.add_apply, Pi.smul_apply, smul_add] <;>
    ring
