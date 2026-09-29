-- Prove2me | Theorems.Thm_lean_workbook_plus_46998
-- name    : lean_workbook_plus_46998
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/05c5a4e9-c32f-448f-8ecb-f3c4bfbecf5c
-- statement:
--   If a,b,c>0 , prove that:\n $ \ 5(a^3+b^3+c^3)+3(a^2 b+b^2 c+c^2 a ) \ge 6(ab^2+b c^2+ca^2) +6abc $\n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46998 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 5 * (a ^ 3 + b ^ 3 + c ^ 3) + 3 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) ≥ 6 * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) + 6 * a * b * c   :=  by sorry
