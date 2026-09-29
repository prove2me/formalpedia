-- Prove2me | Theorems.Thm_lean_workbook_plus_18570
-- name    : lean_workbook_plus_18570
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/8de1bf47-6036-4bfd-b9fe-c03b707e4c97
-- statement:
--   Solve $9-x^2 \ge 0$ , and get $-3 \le x \le 3$ .9-x^2 has a maximum at x=0, where the function is 3. It has a minimum when x=-3,3, and the function is o. So the domain is [-3,3] and the range is [0,3]
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18570  (x : ℝ)
  (h₀ : 9 - x^2 ≥ 0) :
  -3 ≤ x ∧ x ≤ 3   :=  by sorry
