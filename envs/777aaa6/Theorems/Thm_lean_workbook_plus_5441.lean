-- Prove2me | Theorems.Thm_lean_workbook_plus_5441
-- name    : lean_workbook_plus_5441
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/a7768f38-9e1d-4f4d-b936-66d79c80cbe3
-- statement:
--   $f(0)=f(0)^2$ and so $f(0)\in\{0,1\}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5441 (f : ℕ → ℕ) (h : f 0 = f 0 ^ 2) : f 0 = 0 ∨ f 0 = 1   :=  by sorry
