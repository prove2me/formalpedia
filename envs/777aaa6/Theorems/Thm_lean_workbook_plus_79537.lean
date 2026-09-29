-- Prove2me | Theorems.Thm_lean_workbook_plus_79537
-- name    : lean_workbook_plus_79537
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/e1bf37c9-c897-4b87-b6c1-6ad94b83a8ee
-- statement:
--   $\frac{GD}{AC}=\frac{BD}{AB} \rightarrow GD \cdot AB=BD \cdot AC$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79537 {ac ab bd gd: ℝ} (h : ab ≠ 0 ∧ ac ≠ 0 ∧ bd ≠ 0 ∧ gd ≠ 0) : (gd/ac) = (bd/ab) → gd * ab = bd * ac   :=  by sorry
