-- Prove2me | Theorems.Thm_lean_workbook_plus_27297
-- name    : lean_workbook_plus_27297
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/3bcae90d-a93a-4a91-a511-dade05ce9f93
-- statement:
--   $\frac{(x-2){{(x+1)}^{2}}}{(x-3)}<0\Leftrightarrow \left( \frac{x-2}{x-3}<0,x+1\ne 0 \right)\Leftrightarrow \left( 2<x<3,x\ne -1 \right)\Leftrightarrow x\in (2,3)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27297 (x : ℝ) (hx: x ≠ -1) (h : x ≠ 3): (x-2)*(x+1)^2/(x-3) < 0 ↔ 2 < x ∧ x < 3   :=  by sorry
