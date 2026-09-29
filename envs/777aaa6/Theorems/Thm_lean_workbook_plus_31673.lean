-- Prove2me | Theorems.Thm_lean_workbook_plus_31673
-- name    : lean_workbook_plus_31673
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/e7088390-3fab-4b10-97fc-65ae45454908
-- statement:
--   Prove that $\frac{a^2}{a-1}\geq4$ for $a>1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31673 (a : ℝ) (ha : 1 < a) : a^2 / (a - 1) ≥ 4   :=  by sorry
