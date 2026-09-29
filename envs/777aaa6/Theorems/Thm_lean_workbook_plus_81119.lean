-- Prove2me | Theorems.Thm_lean_workbook_plus_81119
-- name    : lean_workbook_plus_81119
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/a2a6da30-876f-452e-87c7-12c14307a01c
-- statement:
--   $ \frac{S}{E+G+I}=20 \Rightarrow E+G+I=\frac{S}{20} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81119 (S E G I : ℝ) : S / (E + G + I) = 20 → E + G + I = S / 20   :=  by sorry
