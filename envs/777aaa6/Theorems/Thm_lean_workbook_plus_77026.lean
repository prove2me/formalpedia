-- Prove2me | Theorems.Thm_lean_workbook_plus_77026
-- name    : lean_workbook_plus_77026
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/56e615e1-05a6-457f-9cf3-5a828f076f7e
-- statement:
--   $ \Leftrightarrow abc(a + b + c)\le a^2b^2 + b^2c^2 + c^2a^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77026 {a b c : ℝ} : a * b * c * (a + b + c) ≤ a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2   :=  by sorry
