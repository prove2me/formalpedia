-- Prove2me | Theorems.Thm_WorkbookSource_base_2864
-- name    : WorkbookSource.base_2864
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:02:29.046693+00:00
-- url     : https://prove2.me/theorems/b935ac5c-9140-49c0-b7db-5a65d0624e9e
-- title:
--   A cyclic cubic-over-quadratic lower bound at fixed sum three
-- statement:
--   If $a, b, c>0, a+b+c=3$ prove that $\frac{a^3}{a^2+bc+ca}+\frac{b^3}{b^2+ca+ab}+\frac{c^3}{c^2+ab+bc}\ge1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2864` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2864; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2864 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a^3 / (a^2 + b * c + c * a) + b^3 / (b^2 + c * a + a * b) + c^3 / (c^2 + a * b + b * c) ≥ 1  :=  by sorry
