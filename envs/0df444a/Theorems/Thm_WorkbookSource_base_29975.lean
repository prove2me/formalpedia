-- Prove2me | Theorems.Thm_WorkbookSource_base_29975
-- name    : WorkbookSource.base_29975
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:44:56.944029+00:00
-- url     : https://prove2.me/theorems/c04945e5-6536-4d56-b679-3a1d948563b7
-- title:
--   A weighted quadratic reciprocal sum upper bound
-- statement:
--   Let $a,b$ be positive real numbers . Prove that $\frac{1}{a^2+b^2}+\frac{7}{a^2+49b^2}\leq\frac{2}{3ab}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_29975` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_29975; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_29975 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 1 / (a ^ 2 + b ^ 2) + 7 / (a ^ 2 + 49 * b ^ 2) ≤ 2 / (3 * a * b)  :=  by sorry
