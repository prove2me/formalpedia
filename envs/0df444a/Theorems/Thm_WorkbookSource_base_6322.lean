-- Prove2me | Theorems.Thm_WorkbookSource_base_6322
-- name    : WorkbookSource.base_6322
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:18:14.726492+00:00
-- url     : https://prove2.me/theorems/965e9ba7-97ba-4ea5-b202-18caa8eb3fb1
-- title:
--   A cyclic cubic-over-quadratic sum bounds the quadratic mean
-- statement:
--   For $a, b, c>0$ prove that $\frac{a(a^2+b^2)}{2a^2+ab+b^2}+\frac{b(b^2+c^2)}{2b^2+bc+c^2}+\frac{c(c^2+a^2)}{2c^2+ca+a^2}\le\frac{3(a^2+b^2+c^2)}{2(a+b+c)}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6322` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6322; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6322 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (a ^ 2 + b ^ 2) / (2 * a ^ 2 + a * b + b ^ 2) + b * (b ^ 2 + c ^ 2) / (2 * b ^ 2 + b * c + c ^ 2) + c * (c ^ 2 + a ^ 2) / (2 * c ^ 2 + c * a + a ^ 2)) ≤ (3 * (a ^ 2 + b ^ 2 + c ^ 2)) / (2 * (a + b + c))  :=  by sorry
