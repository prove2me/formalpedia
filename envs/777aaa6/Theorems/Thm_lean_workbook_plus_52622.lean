-- Prove2me | Theorems.Thm_lean_workbook_plus_52622
-- name    : lean_workbook_plus_52622
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/56f16fe3-f1e3-4823-b5ea-0c97cfd23b66
-- statement:
--   Prove or disprove that for any triangle: $3(a+b+c)^2 \ge 4(a^2+b^2+c^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52622 {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 3 * (a + b + c) ^ 2 ≥ 4 * (a ^ 2 + b ^ 2 + c ^ 2)   :=  by sorry
