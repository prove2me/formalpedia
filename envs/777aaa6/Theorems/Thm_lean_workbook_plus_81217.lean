-- Prove2me | Theorems.Thm_lean_workbook_plus_81217
-- name    : lean_workbook_plus_81217
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/3450a564-229e-4eee-836e-bea36facf30d
-- statement:
--   $ x\le \frac{1}{\sqrt 3} \to 1 \ge x\sqrt 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81217 (x : ℝ) (hx : x ≤ 1 / Real.sqrt 3) : 1 ≥ x * Real.sqrt 3   :=  by sorry
