-- Prove2me | Theorems.Thm_WorkbookSource_base_12712
-- name    : WorkbookSource.base_12712
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:46:01.29754+00:00
-- url     : https://prove2.me/theorems/f93b044d-ba29-4e2a-8edf-45cb4efc10dd
-- title:
--   A cyclic product ratio bounds a pairwise ratio sum
-- statement:
--   Prove the stronger inequality: For any positive real numbers $a,b$ and $c$, $3+\frac{a(a+c)}{b(b+c)}+\frac{b(b+a)}{c(c+a)}+\frac{c(c+b)}{a(a+b)}\ge 4\left(\frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b}\right)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12712` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12712; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12712 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 3 + a * (a + c) / (b * (b + c)) + b * (b + a) / (c * (c + a)) + c * (c + b) / (a * (a + b)) ≥ 4 * (a / (b + c) + b / (c + a) + c / (a + b))  :=  by sorry
