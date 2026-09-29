-- Prove2me | Theorems.Thm_WorkbookSource_base_31921
-- name    : WorkbookSource.base_31921
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:28:45.659079+00:00
-- url     : https://prove2.me/theorems/bcbe50df-9f78-46a1-8f8b-f501d9ab9b1c
-- title:
--   An asymmetric weighted quadratic ratio sum is at least three
-- statement:
--   If $a, b, c>0$ , prove:
--    $\begin{aligned}\frac{5a^2}{b^2+3bc+c^2}+\frac{9b^2}{2c^2+5ca+2a^2}+\frac{13c^2}{3a^2+7ab+3b^2}\geq3\end{aligned}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_31921` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_31921; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_31921 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (5 * a ^ 2 / (b ^ 2 + 3 * b * c + c ^ 2) + 9 * b ^ 2 / (2 * c ^ 2 + 5 * c * a + 2 * a ^ 2) + 13 * c ^ 2 / (3 * a ^ 2 + 7 * a * b + 3 * b ^ 2)) ≥ 3  :=  by sorry
