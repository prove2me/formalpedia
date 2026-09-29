-- Prove2me | Theorems.Thm_lean_workbook_plus_12883
-- name    : lean_workbook_plus_12883
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/c4786f9c-9640-4044-b164-c693f5599f33
-- statement:
--   You have $4x^2-40x+51>0$ for all $x<1.5$ or $x>8.5$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12883 ∀ x:ℝ, (x<1.5 ∨ x>8.5) ↔ (4*x^2-40*x+51>0)   :=  by sorry
