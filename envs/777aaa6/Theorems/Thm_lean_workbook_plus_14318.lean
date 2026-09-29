-- Prove2me | Theorems.Thm_lean_workbook_plus_14318
-- name    : lean_workbook_plus_14318
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/f81ed27e-6982-4522-a436-2a18a3a855c1
-- statement:
--   Prove $\frac{k}{k+1} + \frac{1}{(k+1)(k+2)} = \frac{k+1}{k+2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14318 (k : ℕ) : (k : ℚ) / (k + 1) + 1 / ((k + 1) * (k + 2)) = (k + 1) / (k + 2)   :=  by sorry
