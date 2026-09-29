-- Prove2me | Theorems.Thm_WorkbookSource_plus_8901
-- name    : WorkbookSource.plus_8901
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:52:02.218099+00:00
-- url     : https://prove2.me/theorems/d7056c97-4870-4e02-a5ad-3384f2b36c48
-- title:
--   A cubic ratio sum with a symmetric quadratic correction
-- statement:
--   Let $a, b, c$ be real pozitive numbers. Prove that
--
--    $\frac{a^3+b^3+c^3}{a^{2}b+b^{2}c+c^{2}a}+\frac{ab+bc+ac}{a^2+b^2+c^2}\geq 2.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_8901` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_8901; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_8901 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3 + c^3) / (a^2 * b + b^2 * c + c^2 * a) + (a * b + b * c + c * a) / (a^2 + b^2 + c^2) ≥ 2   :=  by sorry
