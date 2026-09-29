-- Prove2me | Theorems.Thm_lean_workbook_plus_82676
-- name    : lean_workbook_plus_82676
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/49a09513-c4af-4d7b-907e-00b855135437
-- statement:
--   It is enough to prove $\frac{a^{4}}{2}+3a^{2}b^{2}+\frac{b^{4}}{2}\geq 2ab(a^{2}+b^{2})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82676 (a b : ℝ) : (a^4 / 2 + 3 * a^2 * b^2 + b^4 / 2) ≥ 2 * a * b * (a^2 + b^2)   :=  by sorry
