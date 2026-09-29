-- Prove2me | solution 1 for one_plus_exp_pos
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:26:26.514247+00:00
-- url     : https://prove2.me/submissions/52bd9ed7-c530-4caa-963a-a3eb70a75f1b

-- Sol generated from Applications/One_plus_exp_pos.lean
import Mathlib

/-! # CatalogBuild.Shared.One_plus_exp_pos

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 2
-/

noncomputable section




theorem solution(x : ℝ) : (1 : ℝ) + Real.exp x > 0 := by
  linarith [Real.exp_pos x]
