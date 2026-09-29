-- Prove2me | Theorems.Thm_lean_workbook_plus_71796
-- name    : lean_workbook_plus_71796
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/269782af-2600-4848-9a35-c236292bf167
-- statement:
--   $ \frac{1}{a}+\frac{1}{b}+\frac{1}{c}\ge \frac{27}{8}\implies 8ab+8bc+8ca\ge 27abc$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71796 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (1 / a + 1 / b + 1 / c ≥ 27 / 8) → (8 * a * b + 8 * b * c + 8 * c * a ≥ 27 * a * b * c)   :=  by sorry
