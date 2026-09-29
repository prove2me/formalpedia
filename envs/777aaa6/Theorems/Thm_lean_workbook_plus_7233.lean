-- Prove2me | Theorems.Thm_lean_workbook_plus_7233
-- name    : lean_workbook_plus_7233
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/838dc3e1-7bf5-4a46-93b7-d3cbbc9871ff
-- statement:
--   Prove that $ x(1 - x)(x^{4}(x^{2}+x+1) + 1) < 1$ for $x \in (0,1)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7233 : ∀ x : ℝ, x ∈ Set.Ioo 0 1 → x * (1 - x) * (x ^ 4 * (x ^ 2 + x + 1) + 1) < 1   :=  by sorry
