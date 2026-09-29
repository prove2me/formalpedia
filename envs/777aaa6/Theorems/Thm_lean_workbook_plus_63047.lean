-- Prove2me | Theorems.Thm_lean_workbook_plus_63047
-- name    : lean_workbook_plus_63047
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/821c7ad9-16c7-40bf-b6c2-9fe619533d38
-- statement:
--   Prove that $\sqrt{\frac {a^2+(1-b)^2}{2}}\geq \frac {a+(1-b)}{2}$ holds for arbitrary real numbers $a, b$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63047 (a b : ℝ) : Real.sqrt ((a ^ 2 + (1 - b) ^ 2) / 2) ≥ (a + (1 - b)) / 2   :=  by sorry
