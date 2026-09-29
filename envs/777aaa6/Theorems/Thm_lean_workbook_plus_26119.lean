-- Prove2me | Theorems.Thm_lean_workbook_plus_26119
-- name    : lean_workbook_plus_26119
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/77e093fc-1066-439c-bf3b-d4b6ef3a11c2
-- statement:
--   If a number $\overline{abc}$ is a multiple of $3$ , then $\overline{cba}$ also has to be a multiple of $3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26119 (a b c : ℕ) (hab : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9) (h : 3 ∣ a + b + c) : 3 ∣ c + b + a   :=  by sorry
