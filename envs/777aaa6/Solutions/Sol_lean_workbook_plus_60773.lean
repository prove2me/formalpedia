-- Prove2me | solution 1 for lean_workbook_plus_60773
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:02:57.619711+00:00
-- url     : https://prove2.me/submissions/29120d53-5eca-4078-b68c-0a3ff1c067cc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ E D : Set ℚ, (E ∪ D = ℚ ∧ E ≠ ∅ ∧ D ≠ ∅ ∧ ∀ e ∈ E, ∀ d ∈ D, e < d) ↔ E ∪ D = ℚ ∧ E ≠ ∅ ∧ D ≠ ∅ ∧ ∀ e ∈ E, ∀ d ∈ D, e < d := by
  norm_num
