-- Prove2me | Theorems.Thm_lean_workbook_plus_49748
-- name    : lean_workbook_plus_49748
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/e63801ba-4e53-4495-bea5-0497680509e7
-- statement:
--   Prove $ \frac{3}{2}(a^4 + b^4 + c^4 + d^4)\geq{a^2b^2+a^2c^2+a^2d^2+b^2c^2+b^2d^2+c^2d^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49748 (a b c d : ℝ) : (3 / 2) * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) ≥ a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + a ^ 2 * d ^ 2 + b ^ 2 * c ^ 2 + b ^ 2 * d ^ 2 + c ^ 2 * d ^ 2   :=  by sorry
