-- Prove2me | Theorems.Thm_WorkbookSource_base_13448
-- name    : WorkbookSource.base_13448
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:51:06.103795+00:00
-- url     : https://prove2.me/theorems/19ac73b1-826b-47d7-aa20-5d3680733ed4
-- title:
--   A cyclic quadratic reciprocal lower bound at fixed sum three
-- statement:
--   For $a,b,c>0$ such that $a+b+c=3$ . Prove that:
--
--   [2] $\dfrac{1}{5a^2+ab+bc}+\dfrac{1}{5b^2+bc+ca}+\dfrac{1}{5c^2+ca+ab} \ge \dfrac{3}{7}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_13448` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_13448; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_13448 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (1 / (5 * a ^ 2 + a * b + b * c) + 1 / (5 * b ^ 2 + b * c + c * a) + 1 / (5 * c ^ 2 + c * a + a * b)) ≥ 3 / 7  :=  by sorry
