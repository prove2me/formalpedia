-- Prove2me | Theorems.Thm_lean_workbook_plus_73848
-- name    : lean_workbook_plus_73848
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/0180e49f-6d5f-4f55-a1c2-589c6982a00d
-- statement:
--   Prove that $\max \{x,y\} = \dfrac {|x-y| +x+y}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73848 (x y : ℝ) : max x y = (|x - y| + x + y) / 2   :=  by sorry
