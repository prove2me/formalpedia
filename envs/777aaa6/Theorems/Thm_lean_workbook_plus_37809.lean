-- Prove2me | Theorems.Thm_lean_workbook_plus_37809
-- name    : lean_workbook_plus_37809
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/9754dd5c-eafc-4ba1-8669-02f2ca737152
-- statement:
--   Or, since all terms are positive,\n\n $z_1=2(\cos(u)\cos(v)-\sin(u)\sin(v))=2\cos(u+v)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37809 : 2 * (Real.cos u * Real.cos v - Real.sin u * Real.sin v) = 2 * Real.cos (u + v)   :=  by sorry
