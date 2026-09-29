-- Prove2me | Theorems.Thm_lean_workbook_plus_80718
-- name    : lean_workbook_plus_80718
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/368bf66d-16e8-49a4-8b1d-3f201c79ca45
-- statement:
--   What is the greatest value of $\sin x \cos y + \sin y \cos z + \sin z \cos x$ , where $x,y,z$ are real numbers?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80718 (x y z : ℝ) : (sin x * cos y + sin y * cos z + sin z * cos x) ≤ 3 / 2   :=  by sorry
