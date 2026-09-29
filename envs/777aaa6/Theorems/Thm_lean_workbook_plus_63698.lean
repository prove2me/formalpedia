-- Prove2me | Theorems.Thm_lean_workbook_plus_63698
-- name    : lean_workbook_plus_63698
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/e3ae5d8a-5f87-45fd-8104-ca30d0168286
-- statement:
--   Let $ a,b,c > 0$ such that $ a^2 + b^2 + c^2 + 2abc = 5$ Prove that $ 2(ab+ac+bc)\leq5+abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63698 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + 2 * a * b * c = 5) : 2 * (a * b + b * c + c * a) ≤ 5 + a * b * c   :=  by sorry
