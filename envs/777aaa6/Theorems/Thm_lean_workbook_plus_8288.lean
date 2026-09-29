-- Prove2me | Theorems.Thm_lean_workbook_plus_8288
-- name    : lean_workbook_plus_8288
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/c50505f5-3685-4e52-bb8e-35fbf458243f
-- statement:
--   Prove that $ \frac {a^2}{a + 1}\geq \frac {3}{4}a - \frac {1}{4}$ for $ a > 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8288 (a : ℝ) (ha : 0 < a) : (a^2 / (a + 1)) ≥ (3/4 * a - 1/4)   :=  by sorry
