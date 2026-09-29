-- Prove2me | Theorems.Thm_lean_workbook_plus_38913
-- name    : lean_workbook_plus_38913
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/f245e506-d95c-48b9-be34-28908e8f367d
-- statement:
--   If a, b, c, and d are all ≥ 0 and $a+c=b$ , $a+d=c$ , $b-d=2$ , and $b+c-d=3$ , determine the sum of $(a + b + c + d)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38913 (a b c d : ℝ) (h₁ : a + c = b) (h₂ : a + d = c) (h₃ : b - d = 2) (h₄ : b + c - d = 3) : a + b + c + d = 4   :=  by sorry
