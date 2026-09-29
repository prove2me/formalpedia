-- Prove2me | Theorems.Thm_lean_workbook_plus_60336
-- name    : lean_workbook_plus_60336
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/a5050888-6cac-4b7c-921a-6347d8a2e160
-- statement:
--   Prove that $\cos 36^\circ-\cos 72^\circ=\sin 54^\circ-\sin 18^\circ$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60336 : Real.cos (36 * Real.pi / 180) - Real.cos (72 * Real.pi / 180) = Real.sin (54 * Real.pi / 180) - Real.sin (18 * Real.pi / 180)   :=  by sorry
