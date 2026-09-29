-- Prove2me | Theorems.Thm_WorkbookSource_base_27490
-- name    : WorkbookSource.base_27490
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:46:22.64166+00:00
-- url     : https://prove2.me/theorems/27088e32-ebd2-4e9b-a38a-7c72d03a60c2
-- title:
--   An asymmetric weighted pairwise ratio sum is at least four
-- statement:
--   Prove that for any three positive reals a, b, c, the following inequality holds:
--   $\frac{2a}{b+c}+\frac{6b}{c+a}+\frac{3c}{a+b} \ge 4$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_27490` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_27490; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_27490 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 * a / (b + c) + 6 * b / (c + a) + 3 * c / (a + b)) ≥ 4  :=  by sorry
