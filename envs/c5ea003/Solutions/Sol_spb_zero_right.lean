-- Prove2me | solution 1 for spb_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T21:19:14.878716+00:00
-- url     : https://prove2.me/submissions/59b03a9f-124f-4eca-bec3-b347d02edc74

-- Sol generated from Shared/AbstractAlgebra/Spb_zero_right.lean
import Mathlib
import Definitions.Def_Shared_AbstractAlgebra_Spb_zero_right

open Real

/-! # CatalogBuild.Shared.Spb_zero_right

Auto-generated from theorem catalog database.
Domain: Bridges
Declarations: 14
-/


noncomputable section

















theorem solution(x : ℝ) : spb x 0 = x := by
  simp [spb]
