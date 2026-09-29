-- Prove2me | Theorems.Thm_lean_workbook_plus_15300
-- name    : lean_workbook_plus_15300
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/1813c3d6-e55b-4827-bee0-0be5e1e66690
-- statement:
--   $x>0\Longrightarrow \sqrt x\le \frac{1+x}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15300 (x : ℝ) (hx : 0 < x) : Real.sqrt x ≤ (1 + x) / 2   :=  by sorry
