-- Prove2me | Theorems.Thm_lean_workbook_plus_13938
-- name    : lean_workbook_plus_13938
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/49108929-78e9-42ee-b8c8-feda34c47a0d
-- statement:
--   $= \frac{1}{\sqrt{97}}(16(\frac{a}{4} + \frac{1}{9a} + \frac{b}{4} + \frac{1}{9b} + \frac{c}{4} + \frac{1}{9c}) + 65(\frac{1}{9a} + \frac{1}{9b} + \frac{1}{9c}))$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13938 (a b c : ℝ) : (1 / Real.sqrt 97) * (16 * (a / 4 + b / 4 + c / 4) + 65 * (1 / 9 * a + 1 / 9 * b + 1 / 9 * c)) = (1 / Real.sqrt 97) * (16 * (a / 4 + b / 4 + c / 4) + 65 * (1 / 9 * a + 1 / 9 * b + 1 / 9 * c))   :=  by sorry
