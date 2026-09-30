-- Prove2me | solution 1 for lean_workbook_plus_72488
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:34:54.665468+00:00
-- url     : https://prove2.me/submissions/877f5ff8-0178-4be4-bb61-1f8579e3ee00

import Mathlib

theorem solution : ∀ a b : ℝ,
    2 + (|a| + |b|) / 2008 ≥ 1 + |a-b| / 2008 := by
  intro a b
  have h := abs_sub a b
  linarith

#print axioms solution
