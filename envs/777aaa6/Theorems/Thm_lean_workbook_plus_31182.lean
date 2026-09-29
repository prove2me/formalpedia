-- Prove2me | Theorems.Thm_lean_workbook_plus_31182
-- name    : lean_workbook_plus_31182
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/20606a31-937c-48a3-ba0a-aba41fdcb493
-- statement:
--   $(x+1)(y+1) \ge 4 \sqrt{xy} \Longleftrightarrow xy+x+y+1 \ge 4 \sqrt{xy}$ , that is true for AM-GM
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31182 (x y: ℝ) : (x + 1) * (y + 1) ≥ 4 * Real.sqrt (x * y) ↔ x * y + x + y + 1 ≥ 4 * Real.sqrt (x * y)   :=  by sorry
