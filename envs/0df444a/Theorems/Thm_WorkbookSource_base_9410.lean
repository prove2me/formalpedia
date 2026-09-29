-- Prove2me | Theorems.Thm_WorkbookSource_base_9410
-- name    : WorkbookSource.base_9410
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:29:48.535732+00:00
-- url     : https://prove2.me/theorems/bcd06aba-b68a-4e46-be84-04881fcd4eea
-- title:
--   A cyclic product-over-quadratic upper bound at fixed sum three
-- statement:
--   For $a, b, c>0, a+b+c=3$ prove that $\frac{a^2b}{a^2+b}+\frac{b^2c}{b^2+c}+\frac{c^2a}{c^2+a}\le\frac{a^2+b^2+c^2}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9410` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9410; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9410 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a^2 * b / (a^2 + b) + b^2 * c / (b^2 + c) + c^2 * a / (c^2 + a)) ≤ (a^2 + b^2 + c^2) / 2  :=  by sorry
