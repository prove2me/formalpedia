-- Prove2me | Theorems.Thm_lean_workbook_plus_18349
-- name    : lean_workbook_plus_18349
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/8e08f0ea-fbb8-44d2-b99c-da44b829ca2a
-- statement:
--   $ \leftrightarrow a^4+b^4+c^4+6(a^2b^2+b^2c^2+c^2a^2) \ge\ 2\sum ab(a^2+b^2)+ 3abc(a+b+c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18349 (a b c: ℝ) : a^4 + b^4 + c^4 + 6 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) ≥ 2 * (a * b * (a^2 + b^2) + b * c * (b^2 + c^2) + c * a * (c^2 + a^2)) + 3 * a * b * c * (a + b + c)   :=  by sorry
