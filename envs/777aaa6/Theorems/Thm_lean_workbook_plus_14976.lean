-- Prove2me | Theorems.Thm_lean_workbook_plus_14976
-- name    : lean_workbook_plus_14976
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/43a962af-fa71-4b80-ac7f-e5db2f4caa4e
-- statement:
--   Prove (or disproof) that there's no triple $(x, y, z) \in \mathbb R^+$ such that: \n \n \begin{align*}x + y + z &= 20 \\\ xy + yz + xz &= 150\end{align*}
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14976 : ¬ ∃ (x y z : ℝ), (x + y + z = 20 ∧ x*y + y*z + x*z = 150)   :=  by sorry
