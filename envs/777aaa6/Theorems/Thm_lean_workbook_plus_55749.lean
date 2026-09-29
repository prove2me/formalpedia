-- Prove2me | Theorems.Thm_lean_workbook_plus_55749
-- name    : lean_workbook_plus_55749
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/92a3aa92-f888-409f-a331-d2711e5a5c47
-- statement:
--   Let $a, b > 0$ . Prove $(a+b)^{3}+(2a+b)^{3}+(3a)^{3}\le 8(9a^{3}+b^{3})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55749 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a + b) ^ 3 + (2 * a + b) ^ 3 + (3 * a) ^ 3 ≤ 8 * (9 * a ^ 3 + b ^ 3)   :=  by sorry
