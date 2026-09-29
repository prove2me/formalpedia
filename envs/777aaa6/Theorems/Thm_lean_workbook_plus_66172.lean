-- Prove2me | Theorems.Thm_lean_workbook_plus_66172
-- name    : lean_workbook_plus_66172
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/1cc7947e-67d8-4440-8c78-0d3e98013610
-- statement:
--   If $a \ge b \ge 1 \ge c$ , we can use $ab \le 2-c,(b^2-1)(1-c) \ge 0,(a-1)(1-c) \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66172 :  ∀ a b c : ℝ, a ≥ b ∧ b ≥ 1 ∧ 1 ≥ c → a * b ≤ 2 - c ∧ (b ^ 2 - 1) * (1 - c) ≥ 0 ∧ (a - 1) * (1 - c) ≥ 0   :=  by sorry
