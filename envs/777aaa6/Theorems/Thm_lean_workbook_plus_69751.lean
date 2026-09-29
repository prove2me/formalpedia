-- Prove2me | Theorems.Thm_lean_workbook_plus_69751
-- name    : lean_workbook_plus_69751
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/4dcd5a9c-499b-43e8-8b4d-3d97b50c0775
-- statement:
--   Prove that $(a^2+b^2+c^2)(d^2+e^2+f^2)\ge (ad+be+cf)^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69751 (a b c d e f : ℝ) :
  (a^2+b^2+c^2)*(d^2+e^2+f^2) ≥ (a*d+b*e+c*f)^2   :=  by sorry
