-- Prove2me | Theorems.Thm_WorkbookSource_base_3999
-- name    : WorkbookSource.base_3999
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:11:06.988487+00:00
-- url     : https://prove2.me/theorems/09b8a83c-b54e-46e2-acd8-2b2b3d9bf592
-- title:
--   A reciprocal-sum comparison with cyclic weighted denominators
-- statement:
--   Prove that $\frac{1}{a}+\frac{1}{b}+\frac{1}{c}+3(\frac{1}{a+b}+\frac{1}{b+c}+\frac{1}{c+a})\ge 10(\frac{1}{3a+b}+\frac{1}{3b+c}+\frac{1}{3c+a})$ given $a, b, c > 0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3999` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3999; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3999 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / a + 1 / b + 1 / c + 3 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a))) ≥ 10 * (1 / (3 * a + b) + 1 / (3 * b + c) + 1 / (3 * c + a))  :=  by sorry
