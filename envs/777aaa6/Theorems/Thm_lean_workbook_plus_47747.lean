-- Prove2me | Theorems.Thm_lean_workbook_plus_47747
-- name    : lean_workbook_plus_47747
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/1048c667-de49-446e-b5a4-f5e289e9ac00
-- statement:
--   For non-negative real numbers $a$ , $b$ , and $c$ , prove the following $a^{2}(b+c)+b^{2}(a+c)+c^{2}(a+b) \ge 6abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47747 (a b c: ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a^2 * (b + c) + b^2 * (a + c) + c^2 * (a + b) ≥ 6 * a * b * c   :=  by sorry
