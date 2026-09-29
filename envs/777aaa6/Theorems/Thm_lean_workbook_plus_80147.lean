-- Prove2me | Theorems.Thm_lean_workbook_plus_80147
-- name    : lean_workbook_plus_80147
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/0116a207-9b36-48dd-b5aa-484375a34c04
-- statement:
--   And again, the coefficients of the cubic add to $ 0$ . So factor out another $ (x-1)$ : \n $ (x-1)^3 (x^2+6)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80147 {f : ℝ → ℝ} (hf: f x = (x-1)^3 * (x^2+6)) : f x = (x-1)^3 * (x^2+6)   :=  by sorry
