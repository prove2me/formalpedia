-- Prove2me | Theorems.Thm_lean_workbook_plus_73830
-- name    : lean_workbook_plus_73830
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/39225f62-e581-408a-8d1b-052969ebe480
-- statement:
--   prove that $-9a^{2}b^{2}c^{2}\geq-abc(a+b+c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73830 : ∀ a b c : ℝ, -9 * a ^ 2 * b ^ 2 * c ^ 2 ≥ -a * b * c * (a + b + c)   :=  by sorry
