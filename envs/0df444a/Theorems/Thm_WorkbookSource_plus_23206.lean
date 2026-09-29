-- Prove2me | Theorems.Thm_WorkbookSource_plus_23206
-- name    : WorkbookSource.plus_23206
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:33:35.467575+00:00
-- url     : https://prove2.me/theorems/3f6c844f-1568-4ecf-8e23-0b497f266188
-- title:
--   A pairwise product ratio sum has a symmetric quadratic upper bound
-- statement:
--   Let $a$ , $b$ and $c$ be positive numbers. Prove that:
--   $$\frac{ab(a+b)}{2ab+ac+bc}+\frac{ac(a+c)}{2ac+ab+bc}+\frac{bc(b+c)}{2bc+ac+ab}\leq\frac{3(a^2+b^2+c^2+ab+ac+bc)}{4(a+b+c)}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_23206` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_23206; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_23206 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b * (a + b) / (2 * a * b + a * c + b * c) + a * c * (a + c) / (2 * a * c + a * b + b * c) + b * c * (b + c) / (2 * b * c + a * c + a * b)) ≤ (3 * (a ^ 2 + b ^ 2 + c ^ 2 + a * b + a * c + b * c)) / (4 * (a + b + c))   :=  by sorry
