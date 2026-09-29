-- Prove2me | Theorems.Thm_lean_workbook_plus_32505
-- name    : lean_workbook_plus_32505
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/19936535-96a1-4ab9-99ab-1efb97bccece
-- statement:
--   Prove the following inequality:\n\n$\left( xy+xz+yz \right) ^{2}\geq 3\, \left( x+y+z \right) xyz$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32505 (x y z : ℝ) : (x * y + x * z + y * z) ^ 2 ≥ 3 * (x + y + z) * x * y * z   :=  by sorry
