-- Prove2me | Theorems.Thm_lean_workbook_plus_52990
-- name    : lean_workbook_plus_52990
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/af011d4d-8079-467a-a82d-e5853b60fec0
-- statement:
--   For $2<x\leq 3; f(x) =-(x-3)-(x-4)=-2x+7$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52990 (x : ℝ) (h₁ : 2 < x) (h₂ : x ≤ 3) : -(x - 3) - (x - 4) = -2 * x + 7   :=  by sorry
