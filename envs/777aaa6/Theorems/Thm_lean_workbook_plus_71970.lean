-- Prove2me | Theorems.Thm_lean_workbook_plus_71970
-- name    : lean_workbook_plus_71970
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/9e87e1a0-8c8a-4ac9-9976-ce2f9fbad5ee
-- statement:
--   Write as $E=a\sin u + b\sin (u+v) =(a+b\cos v)\sin u + (b\sin v)\cos u$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71970 (a b : ℝ) (u v : ℝ) : a * sin u + b * sin (u + v) = (a + b * cos v) * sin u + (b * sin v) * cos u   :=  by sorry
