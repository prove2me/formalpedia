-- Prove2me | solution 1 for lean_workbook_plus_67335
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:02:07.640199+00:00
-- url     : https://prove2.me/submissions/5ab3c109-ceeb-44c3-8a8a-d0ffcb846bff

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p q : Prop) : (p → q) → (¬¬p → q) := by
  norm_num
