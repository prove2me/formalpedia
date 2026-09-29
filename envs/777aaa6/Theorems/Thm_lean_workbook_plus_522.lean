-- Prove2me | Theorems.Thm_lean_workbook_plus_522
-- name    : lean_workbook_plus_522
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/cf976863-9a31-48eb-a379-45cd113fbc1b
-- statement:
--   If $ x_1,x_2,...,x_n \ge 0$ then $ x_1^2+x_2^2+...+x_n^2 \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_522 (n : ℕ) (x : ℕ → ℝ) : ∀ i : ℕ, i ≤ n → x i ≥ 0 → ∑ i in Finset.range n, (x i)^2 ≥ 0   :=  by sorry
