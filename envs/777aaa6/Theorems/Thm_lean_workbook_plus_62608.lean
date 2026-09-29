-- Prove2me | Theorems.Thm_lean_workbook_plus_62608
-- name    : lean_workbook_plus_62608
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/e67d6a06-a7c3-4adc-b47f-266f9738ed3d
-- statement:
--   Prove that $\sin 30^{\circ}=3\sin 10^{\circ}-4\sin ^3 10^{\circ}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62608 : sin 30 = 3 * sin 10 - 4 * (sin 10)^3   :=  by sorry
