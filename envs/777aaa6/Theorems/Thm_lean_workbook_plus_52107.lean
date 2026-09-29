-- Prove2me | Theorems.Thm_lean_workbook_plus_52107
-- name    : lean_workbook_plus_52107
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/d6be5b83-1cfb-44d7-92f3-66955e6ae621
-- statement:
--   $=\left(a-\frac{b+c}{2}\right)^2+\frac{3}{4}(b-c)^2\geq 0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52107 (a b c : ℝ) :
  (a - (b + c) / 2)^2 + (3 / 4) * (b - c)^2 ≥ 0   :=  by sorry
