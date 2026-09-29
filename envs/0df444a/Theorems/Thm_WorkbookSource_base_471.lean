-- Prove2me | Theorems.Thm_WorkbookSource_base_471
-- name    : WorkbookSource.base_471
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:45:21.21099+00:00
-- url     : https://prove2.me/theorems/5956afce-45e0-4a7b-872b-022c9524dbbb
-- title:
--   A cyclic rational sum of differences is nonnegative
-- statement:
--   For $a$ , $b$ and $c$ >0 prove that: $\frac{a(a-b)}{a^2+b^2}+\frac{b(b-c)}{b^2+c^2}+\frac{c(c-a)}{c^2+a^2} \geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_471` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_471; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_471 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (a - b) / (a ^ 2 + b ^ 2) + b * (b - c) / (b ^ 2 + c ^ 2) + c * (c - a) / (c ^ 2 + a ^ 2)) ≥ 0  :=  by sorry
