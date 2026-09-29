-- Prove2me | Theorems.Thm_lean_workbook_plus_14386
-- name    : lean_workbook_plus_14386
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/19d31a8d-5087-4556-8d75-bf7a14d22550
-- statement:
--   Prove that for all real $a,$ $b$ and $c$ the following inequality holds: \n $a^{4}b^{2}+b^{4}c^{2}+c^{4}a^{2}\geq a^{3}c^{2}b+b^{3}a^{2}c+c^{3}b^{2}a.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14386 (a b c : ℝ) : a ^ 4 * b ^ 2 + b ^ 4 * c ^ 2 + c ^ 4 * a ^ 2 ≥ a ^ 3 * c ^ 2 * b + b ^ 3 * a ^ 2 * c + c ^ 3 * b ^ 2 * a   :=  by sorry
