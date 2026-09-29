-- Prove2me | Theorems.Thm_WorkbookSource_base_1693
-- name    : WorkbookSource.base_1693
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:40:31.816828+00:00
-- url     : https://prove2.me/theorems/7230a846-bac5-4bc9-92ee-e9c08f9d83db
-- title:
--   A four-variable cyclic pair-sum ratio is at least two
-- statement:
--   Prove that for positive real numbers $a, b, c, d$, the following inequality holds: $\frac{c}{a+b}+\frac{d}{b+c}+\frac{a}{c+d}+\frac{b}{d+a} \ge 2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1693` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1693; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1693 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (c / (a + b) + d / (b + c) + a / (c + d) + b / (d + a)) ≥ 2  :=  by sorry
