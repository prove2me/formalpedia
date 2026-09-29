-- Prove2me | Theorems.Thm_lean_workbook_plus_41791
-- name    : lean_workbook_plus_41791
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/0f754aee-8716-45a3-a413-72af5089d865
-- statement:
--   Prove that the number $9\cdot 2^{511}+1$ is not odd.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41791 : ¬(9 * 2 ^ 511 + 1) % 2 = 1   :=  by sorry
