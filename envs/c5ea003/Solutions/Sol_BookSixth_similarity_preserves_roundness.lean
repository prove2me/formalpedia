-- Prove2me | solution 1 for BookSixth.similarity_preserves_roundness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-25T16:48:48.441064+00:00
-- url     : https://prove2.me/submissions/c4c55bd4-a2b6-46a9-b69a-a952ea65df65

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

/-- A similarity `x ↦ a • x + b` with positive scale maps a round circle to a round
circle. The witness keeps the orthonormal frame `u`, `v` and replaces the centre by
`a • c + b` and the radius by `a * r`; this is why the three orthonormal equations
are reused verbatim rather than reproved. -/
theorem solution (C : Set Space3) (a : ℝ) (b : Space3) (ha : 0 < a)
    (hC : RoundCircle C) :
    RoundCircle ((fun x : Space3 => a • x + b) '' C) := by
  obtain ⟨c, u, v, r, hr, hu, hv, huv, hCeq⟩ := hC
  refine ⟨a • c + b, u, v, a * r, mul_pos ha hr, hu, hv, huv, ?_⟩
  rw [hCeq, ← Set.range_comp]
  congr 1
  funext t
  funext i
  fin_cases i <;>
    simp [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_add, smul_smul] <;>
    ring
