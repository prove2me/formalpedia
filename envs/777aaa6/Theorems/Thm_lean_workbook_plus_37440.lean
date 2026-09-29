-- Prove2me | Theorems.Thm_lean_workbook_plus_37440
-- name    : lean_workbook_plus_37440
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/65e85014-3fce-435f-b3a9-297980a89d8c
-- statement:
--   Prove that if $a+b+c=1$ then: \na^2+b^2+c^2\ge \frac {1}{3}
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37440 (a b c : ℝ) (habc : a + b + c = 1) : a^2 + b^2 + c^2 ≥ 1/3   :=  by sorry
