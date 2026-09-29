-- Prove2me | Theorems.Thm_lean_workbook_plus_60699
-- name    : lean_workbook_plus_60699
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/f65d8085-bc08-43a5-bb6c-c50a7af5d45a
-- statement:
--   Positive real numbers $x,y,z$ satisfy $xy+yz+xz=27$ . Prove that $x+y+z \geq 9$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60699 (x y z : ℝ) (h : 0 < x ∧ 0 < y ∧ 0 < z) (h' : x * y + y * z + z * x = 27) : x + y + z >= 9   :=  by sorry
