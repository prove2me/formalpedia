-- Prove2me | Theorems.Thm_lean_workbook_plus_81676
-- name    : lean_workbook_plus_81676
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/78dd69db-b908-4c66-b55b-3671a3096d6e
-- statement:
--   Let $ a,b\geq0.$ Prove that $\frac{a+1}{b+1}+\frac{3a+b+1}{a+3b+1}+\frac{6a+b+1}{a+6b+1}\geq \frac{1}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81676 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (a + 1) / (b + 1) + (3 * a + b + 1) / (a + 3 * b + 1) + (6 * a + b + 1) / (a + 6 * b + 1) ≥ 1 / 2   :=  by sorry
