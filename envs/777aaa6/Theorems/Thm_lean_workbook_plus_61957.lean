-- Prove2me | Theorems.Thm_lean_workbook_plus_61957
-- name    : lean_workbook_plus_61957
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/902af3ab-73cd-4d9a-b50d-08809e1f91df
-- statement:
--   Show that $(x-1)(x-2)(x-4)(x-5) \geq \frac{-9}{4}$ for all $x$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61957 : ∀ x, (x - 1) * (x - 2) * (x - 4) * (x - 5) ≥ (-9 / 4)   :=  by sorry
