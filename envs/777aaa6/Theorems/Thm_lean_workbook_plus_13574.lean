-- Prove2me | Theorems.Thm_lean_workbook_plus_13574
-- name    : lean_workbook_plus_13574
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/98f8d2c5-57ee-48b8-98e0-cd8ba49c8b51
-- statement:
--   if $ n=1$ then $ x=y=1$ works, then $ min (1,1)=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13574 (n x y : ℕ) (h₀ : n = 1) (h₁ : x = 1) (h₂ : y = 1) : min x y = 1   :=  by sorry
