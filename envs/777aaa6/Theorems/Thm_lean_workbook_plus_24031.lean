-- Prove2me | Theorems.Thm_lean_workbook_plus_24031
-- name    : lean_workbook_plus_24031
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/4c910ee4-ad42-4d9a-923f-4163dcee487a
-- statement:
--   Prove that $ (1 + a)^x = 1 + ax$ for $ x \in \{0, 1\}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24031 (x : ℝ) (a : ℝ) (h : x = 0 ∨ x = 1) : (1 + a) ^ x = 1 + a * x   :=  by sorry
