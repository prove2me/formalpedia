-- Prove2me | Theorems.Thm_lean_workbook_plus_26398
-- name    : lean_workbook_plus_26398
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/c113f05b-7dfe-44c5-b2dd-53e606553a4a
-- statement:
--   For $ n \in \mathbb R^* $, prove that:\n$ 2^{n + 1} \bigg| \left\lfloor\left(1 + \sqrt {3}\right)^{2n}\right\rfloor + 1. $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26398 (n : ℝ) (hn : n ≠ 0) : (2:ℝ)^(n+1) ∣ (Int.floor ((1 + Real.sqrt 3)^(2 * n))) + 1   :=  by sorry
