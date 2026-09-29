-- Prove2me | solution 1 for spb_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T21:19:14.322826+00:00
-- url     : https://prove2.me/submissions/b1dc104f-1ed3-46b4-a0a0-b6ad7516216d

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

















theorem solution(x : ℝ) : spb 0 x = x := by
  simp [spb]
