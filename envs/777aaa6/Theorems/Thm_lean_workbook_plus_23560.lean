-- Prove2me | Theorems.Thm_lean_workbook_plus_23560
-- name    : lean_workbook_plus_23560
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/796305d9-2b19-4946-9c3e-440fe5b278ad
-- statement:
--   $a^2 + ( - 2cosA)a + cos^2A - 3sin^2A \le 0 \Leftrightarrow (a - cosA + \sqrt3sinA)(a - cosA - \sqrt3sinA) \le 0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23560 (a : ℝ) (A : ℝ) : a^2 + (-2 * Real.cos A) * a + (Real.cos A)^2 - 3 * (Real.sin A)^2 ≤ 0 ↔ (a - Real.cos A + Real.sqrt 3 * Real.sin A) * (a - Real.cos A - Real.sqrt 3 * Real.sin A) ≤ 0   :=  by sorry
