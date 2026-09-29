-- Prove2me | Theorems.Thm_lean_workbook_plus_18048
-- name    : lean_workbook_plus_18048
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/0cbcda3b-bfbc-467c-ad42-dc5aeb7f917b
-- statement:
--   Expanding, this is equivalent to\n $ a^4b^2 + a^2b^4 + 1 \ge a^3b^3 + ab^2 + a^2b$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18048 (a b : ℝ) : a^4 * b^2 + a^2 * b^4 + 1 ≥ a^3 * b^3 + a * b^2 + a^2 * b   :=  by sorry
