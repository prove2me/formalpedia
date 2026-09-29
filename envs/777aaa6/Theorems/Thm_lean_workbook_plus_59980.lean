-- Prove2me | Theorems.Thm_lean_workbook_plus_59980
-- name    : lean_workbook_plus_59980
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/33678a5d-3f05-41a4-94cb-9d17cd895f74
-- statement:
--   Solve the homogeneous part of the differential equation $\frac{d^{2}y}{dx^{2}} + 4 \frac{dy}{dx} +5y=0$ by finding the roots of its characteristic polynomial $r^2+4r+5=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59980 (y : ℝ → ℝ) (h : y'' + 4*y' + 5*y = 0) : (y'' + 4*y' + 5*y = 0) ↔ (r^2 + 4*r + 5 = 0)   :=  by sorry
