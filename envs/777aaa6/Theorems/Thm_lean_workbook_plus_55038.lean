-- Prove2me | Theorems.Thm_lean_workbook_plus_55038
-- name    : lean_workbook_plus_55038
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/9b96470f-efa2-4e6d-9e94-872c7aeb3593
-- statement:
--   Prove that $\\frac{1}{\\sqrt{n}+\\sqrt{n+1}} =\\sqrt{n+1}-\\sqrt{n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55038 (n : ℕ) : 1 / (Real.sqrt n + Real.sqrt (n + 1)) = Real.sqrt (n + 1) - Real.sqrt n   :=  by sorry
