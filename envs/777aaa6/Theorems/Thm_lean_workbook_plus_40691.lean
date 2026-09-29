-- Prove2me | Theorems.Thm_lean_workbook_plus_40691
-- name    : lean_workbook_plus_40691
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/911bce9e-c676-4d81-b63f-7d5b96c6eba4
-- statement:
--   b.) $ \frac{7C2}{14C2}$ = $ 3/13$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40691 (h : 7 < 14) : (Nat.choose 7 2 : ℚ) / (Nat.choose 14 2 : ℚ) = 3 / 13   :=  by sorry
