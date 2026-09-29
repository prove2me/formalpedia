-- Prove2me | Theorems.Thm_lean_workbook_plus_38005
-- name    : lean_workbook_plus_38005
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/3fd26f9b-dcd7-4492-aea5-020b66491caa
-- statement:
--   $ \leftrightarrow t= \frac{1}{\sqrt{3}}$ or $ t= \frac{-1}{\sqrt{3}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38005 (t : ℝ) : (t^2 = 1/3) ↔ t = 1/Real.sqrt 3 ∨ t = -1/Real.sqrt 3   :=  by sorry
