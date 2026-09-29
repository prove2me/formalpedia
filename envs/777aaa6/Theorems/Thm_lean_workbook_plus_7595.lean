-- Prove2me | Theorems.Thm_lean_workbook_plus_7595
-- name    : lean_workbook_plus_7595
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/ebc8df2a-5f10-4f57-9004-9ff98b1db074
-- statement:
--   $a^2b+b^2c+c^2a+abc\le 4\Leftrightarrow a^2b+b^2c+c^2a\le 4-abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7595 (a b c : ℝ) : a^2 * b + b^2 * c + c^2 * a + a * b * c ≤ 4 ↔ a^2 * b + b^2 * c + c^2 * a ≤ 4 - a * b * c   :=  by sorry
