-- Prove2me | Theorems.Thm_lean_workbook_plus_7888
-- name    : lean_workbook_plus_7888
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/bf9ca9fd-3142-459b-a344-b7dbd7717168
-- statement:
--   Squaring both $\sqrt {14}$ and $6-\sqrt{3}$ gives $14$ and $39-12\sqrt{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7888 : (Real.sqrt 14)^2 = 14 ∧ (6 - Real.sqrt 3)^2 = 39 - 12 * Real.sqrt 3   :=  by sorry
