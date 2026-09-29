-- Prove2me | Theorems.Thm_lean_workbook_plus_22638
-- name    : lean_workbook_plus_22638
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/89f6e7a5-e9c8-4a1b-9a5f-b6872e19a3c1
-- statement:
--   The last inequality has real solutions for $a$ only if the discriminant is not negative. $(36K)^2-4\cdot 52(6K^2+3)\geq 0\implies 48K^2\geq 624\implies K^2\geq 13\implies |K|\geq\sqrt{13}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22638 (K : ℝ) : (36 * K) ^ 2 - 4 * 52 * (6 * K ^ 2 + 3) ≥ 0 ↔ |K| ≥ Real.sqrt 13   :=  by sorry
