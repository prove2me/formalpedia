-- Prove2me | Theorems.Thm_lean_workbook_plus_46756
-- name    : lean_workbook_plus_46756
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/1235dfbf-e235-4138-8249-7d2260e5234f
-- statement:
--   Prove that $ 8(a^2b^2 + b^2c^2 + c^2a^2)(a^2 + b^2 + c^2) \le\ 9(a^2 + b^2)(a^2 + c^2)(b^2 + c^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46756 (a b c : ℝ) :
  8 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) * (a^2 + b^2 + c^2) ≤
  9 * (a^2 + b^2) * (a^2 + c^2) * (b^2 + c^2)   :=  by sorry
