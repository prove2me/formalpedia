-- Prove2me | Theorems.Thm_lean_workbook_plus_48094
-- name    : lean_workbook_plus_48094
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/c1dfe620-a464-4e73-82f0-0f6b4cc64183
-- statement:
--   Let $ a,b,c$ be non-negative real numbers. Prove that \n $ 3\sum_{cyc} a^4 + 9\sum_{cyc} a^2b^2\ge 5\sum_{cyc} a^3(b + c) + 2abc\sum_{cyc} a.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48094 (a b c : ℝ) : 3 * (a ^ 4 + b ^ 4 + c ^ 4) + 9 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 5 * (a ^ 3 * (b + c) + b ^ 3 * (c + a) + c ^ 3 * (a + b)) + 2 * a * b * c * (a + b + c)   :=  by sorry
