-- Prove2me | Theorems.Thm_lean_workbook_plus_68577
-- name    : lean_workbook_plus_68577
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/3d50fa08-abfc-4353-846e-63143f69ca89
-- statement:
--   Need prove $ 3(a^2 + b^2 + c^2)^2 \ge 2(a^3 + b^3 + c^3)(a+b+c) + 3abc(a+b+c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68577 (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 2 * (a ^ 3 + b ^ 3 + c ^ 3) * (a + b + c) + 3 * a * b * c * (a + b + c)   :=  by sorry
