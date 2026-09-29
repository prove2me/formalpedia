-- Prove2me | Theorems.Thm_lean_workbook_plus_22781
-- name    : lean_workbook_plus_22781
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/70e87353-be84-465c-b57d-7aaa42b8dfd0
-- statement:
--   Prove that $\frac{1+a_i}{2}\geq\sqrt{1\cdot a_i}\iff1+a_i\geq2\sqrt{a_i}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22781 : 1 + a_i ≥ 2 * Real.sqrt a_i ↔ (1 + a_i) / 2 ≥ Real.sqrt (1 * a_i)   :=  by sorry
