-- Prove2me | Theorems.Thm_WorkbookSource_base_2062
-- name    : WorkbookSource.base_2062
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:56:49.68778+00:00
-- url     : https://prove2.me/theorems/fe2a50fc-3f1e-4078-b02d-945c95ce205d
-- title:
--   A cyclic pairwise ratio bound with a quadratic correction
-- statement:
--   Let $a$ , $b$ and $c$ positive real numbers such that $a+b+c=3$ . Prove that: $\frac{a+b}{b+c}+\frac{b+c}{c+a}+\frac{c+a}{a+b} \geq \frac{a^2+b^2+c^2+9}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2062` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2062; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2062 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b + c = 3) : (a + b) / (b + c) + (b + c) / (c + a) + (c + a) / (a + b) ≥ (a ^ 2 + b ^ 2 + c ^ 2 + 9) / 4  :=  by sorry
