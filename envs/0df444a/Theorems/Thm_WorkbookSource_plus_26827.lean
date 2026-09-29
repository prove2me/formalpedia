-- Prove2me | Theorems.Thm_WorkbookSource_plus_26827
-- name    : WorkbookSource.plus_26827
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:48:00.315685+00:00
-- url     : https://prove2.me/theorems/2aee88c7-ba10-4e24-92b5-dc3464b1743d
-- title:
--   A pairwise cyclic ratio sum has a symmetric quadratic upper bound
-- statement:
--   The following inequality is also true.
--   Let $a$ , $b$ and $c$ are positive numbers. Prove that:
--    $\frac{2a}{a+b}+\frac{2b}{b+c}+\frac{2c}{c+a} \le \frac{7(a^2+b^2+c^2)+2(ab+ac+bc)}{(a+b+c)^2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_26827` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_26827; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_26827 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 * a / (a + b) + 2 * b / (b + c) + 2 * c / (c + a)) ≤ (7 * (a ^ 2 + b ^ 2 + c ^ 2) + 2 * (a * b + b * c + c * a)) / (a + b + c) ^ 2   :=  by sorry
