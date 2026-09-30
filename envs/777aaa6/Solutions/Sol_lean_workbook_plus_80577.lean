-- Prove2me | solution 1 for lean_workbook_plus_80577
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T04:32:13.814816+00:00
-- url     : https://prove2.me/submissions/d2384701-a726-4d87-bc3b-c90bed7c0e8a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

theorem solution : ¬ (∀ x : ℝ, 1 / (3 * x ^ 2 + 1) ≥ (52 - 48 * x) / 49) := by
  intro h
  have hbad := h 0
  norm_num at hbad
