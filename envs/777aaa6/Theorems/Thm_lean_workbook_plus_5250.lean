-- Prove2me | Theorems.Thm_lean_workbook_plus_5250
-- name    : lean_workbook_plus_5250
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/a56376b9-4548-4465-9638-fd38782aeccd
-- statement:
--   Demonstrate the identity: \(\sin(a+x)-\sin(a-x)=2\cos(a)\sin(x)\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5250 (a x : ℝ) : Real.sin (a + x) - Real.sin (a - x) = 2 * Real.cos a * Real.sin x   :=  by sorry
