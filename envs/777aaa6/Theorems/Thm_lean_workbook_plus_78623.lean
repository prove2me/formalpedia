-- Prove2me | Theorems.Thm_lean_workbook_plus_78623
-- name    : lean_workbook_plus_78623
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/6c2b8a1b-d4bb-40d4-9464-0b31345200e5
-- statement:
--   prove that $\sqrt {ab}.(2 - \sqrt {ab})\leq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78623 (a b : ℝ) : Real.sqrt (a * b) * (2 - Real.sqrt (a * b)) ≤ 1   :=  by sorry
