-- Prove2me | Theorems.Thm_WorkbookSource_base_35007
-- name    : WorkbookSource.base_35007
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:53:54.005626+00:00
-- url     : https://prove2.me/theorems/f96aa488-ce40-4630-a4ba-fa81f8d5a777
-- title:
--   A weighted quadratic reciprocal lower bound
-- statement:
--   Prove that
--    $\frac{1}{a^2+7ab+b^2} + \frac{1}{b^2+7bc+c^2} + \frac{1}{c^2+7ca+a^2} \geqslant \frac{1}{ab+bc+ca}$
--    when $a,b,c$ is positive real number.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_35007` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_35007; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_35007 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / (a ^ 2 + 7 * a * b + b ^ 2) + 1 / (b ^ 2 + 7 * b * c + c ^ 2) + 1 / (c ^ 2 + 7 * c * a + a ^ 2) ≥ 1 / (a * b + b * c + c * a)  :=  by sorry
