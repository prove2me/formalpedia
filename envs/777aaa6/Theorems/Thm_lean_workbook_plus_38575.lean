-- Prove2me | Theorems.Thm_lean_workbook_plus_38575
-- name    : lean_workbook_plus_38575
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/74325278-0f00-4a15-b62a-2d517362445c
-- statement:
--   Prove that for any $a \ge b \ge c$ , such that $a,b,c$ are all positive, and $b + c > a$ , that \n\n $a^2b^2 + b^2c^2 +a^2c^2 \ge (a+b+c)(a+b-c)(a-b+c)(b+c-a)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38575 {a b c : ℝ} (h1 : a ≥ b ∧ b ≥ c) (h2 : 0 < a ∧ 0 < b ∧ 0 < c) (h3 : b + c > a) : a^2 * b^2 + b^2 * c^2 + a^2 * c^2 ≥ (a + b + c) * (a + b - c) * (a - b + c) * (b + c - a)   :=  by sorry
