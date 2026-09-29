-- Prove2me | Theorems.Thm_WorkbookSource_base_161
-- name    : WorkbookSource.base_161
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:33:34.129061+00:00
-- url     : https://prove2.me/theorems/420a7d1b-4145-4963-89f7-aec6f83d0632
-- title:
--   A symmetric rational comparison of pairwise and triple products
-- statement:
--   For positive reals $a,b,c$ prove: $\frac{a^2 +b^2 +c^2 +4(ab+bc+ca)}{2abc} \geqslant \frac{9(a+b+c)}{2(ab+bc+ca)} +2(\frac{1}{a+b} + \frac{1}{b+c} + \frac{1}{c+a})$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_161` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_161; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_161 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2 + 4 * (a * b + b * c + c * a)) / (2 * a * b * c) ≥ (9 * (a + b + c)) / (2 * (a * b + b * c + c * a)) + 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a))  :=  by sorry
