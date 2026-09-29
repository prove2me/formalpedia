-- Prove2me | Theorems.Thm_lean_workbook_plus_64932
-- name    : lean_workbook_plus_64932
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/a0981d9f-600d-4a15-8d77-c7fa63f85a93
-- statement:
--   Given $x^3 \equiv 1 \pmod n$, show that $(x-1)(x^2+x+1) \equiv 0 \pmod n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64932 (x n : ℕ) (hx : x^3 ≡ 1 [ZMOD n]) : (x - 1) * (x^2 + x + 1) ≡ 0 [ZMOD n]   :=  by sorry
