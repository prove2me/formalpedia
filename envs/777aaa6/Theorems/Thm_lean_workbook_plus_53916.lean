-- Prove2me | Theorems.Thm_lean_workbook_plus_53916
-- name    : lean_workbook_plus_53916
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/38e313c3-d5f5-4ffd-90fb-f3d39d051438
-- statement:
--   expanding and factorizing, this is just $(a+b)(b+c)(c+a) = 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53916 {a b c : ℂ} : (a + b) * (b + c) * (c + a) = 0 ↔ a = -b ∨ b = -c ∨ c = -a   :=  by sorry
