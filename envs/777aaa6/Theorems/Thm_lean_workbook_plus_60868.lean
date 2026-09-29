-- Prove2me | Theorems.Thm_lean_workbook_plus_60868
-- name    : lean_workbook_plus_60868
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/e70b7b63-a70f-40e1-8c8f-002ead50622e
-- statement:
--   What if we had the system\n$x + y = 2$\n$2x + y = 5$\n$x - y = 4$\nwith solution $(x, y) = (3, -1)$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60868 (x y : ℝ) (h₁ : x + y = 2) (h₂ : 2*x + y = 5) (h₃ : x - y = 4) : x = 3 ∧ y = -1   :=  by sorry
