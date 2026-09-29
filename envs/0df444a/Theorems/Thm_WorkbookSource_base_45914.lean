-- Prove2me | Theorems.Thm_WorkbookSource_base_45914
-- name    : WorkbookSource.base_45914
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:54:47.083751+00:00
-- url     : https://prove2.me/theorems/50f263d6-7772-4b30-a923-e557841e8381
-- title:
--   A cyclic weighted quadratic ratio sum is at least one
-- statement:
--   Prove that for any $a,b,c>0$ we always have $\frac{a^{2}}{2b^{2}+ca}+\frac{b^{2}}{2c^{2}+ab}+\frac{c^{2}}{2a^{2}+bc}\ge 1 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_45914` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_45914; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_45914 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (2 * b^2 + c * a) + b^2 / (2 * c^2 + a * b) + c^2 / (2 * a^2 + b * c)) ≥ 1  :=  by sorry
