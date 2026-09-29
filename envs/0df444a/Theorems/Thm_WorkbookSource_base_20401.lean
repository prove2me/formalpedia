-- Prove2me | Theorems.Thm_WorkbookSource_base_20401
-- name    : WorkbookSource.base_20401
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:45:05.91581+00:00
-- url     : https://prove2.me/theorems/bf3d427b-7792-4e39-b401-927c4b4dbee2
-- title:
--   A reciprocal pair-product sum bounds eight divided by two pair sums
-- statement:
--   Given that $a$, $b$, $c$, and $d$ are positive numbers, prove that $\frac{1}{ab}+\frac{1}{cd}\geq\frac{8}{(a+b)(c+d)}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_20401` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_20401; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_20401 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (1 / (a * b) + 1 / (c * d)) ≥ 8 / (a + b) / (c + d)  :=  by sorry
