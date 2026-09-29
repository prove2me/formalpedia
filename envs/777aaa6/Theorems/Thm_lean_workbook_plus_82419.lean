-- Prove2me | Theorems.Thm_lean_workbook_plus_82419
-- name    : lean_workbook_plus_82419
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/b3a0361d-2a94-479d-8047-b27a0de53119
-- statement:
--   Prove that $\frac{1}{1999}< \prod_{i=1}^{999}{\frac{2i-1}{2i}}<\frac{1}{44}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82419 : (1 / 1999 : ℝ) < ∏ i in Finset.range 999, (2 * i - 1) / (2 * i) ∧ ∏ i in Finset.range 999, (2 * i - 1) / (2 * i) < 1 / 44   :=  by sorry
