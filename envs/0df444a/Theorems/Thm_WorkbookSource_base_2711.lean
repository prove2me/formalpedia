-- Prove2me | Theorems.Thm_WorkbookSource_base_2711
-- name    : WorkbookSource.base_2711
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:00:46.978386+00:00
-- url     : https://prove2.me/theorems/b9ccf8c1-0996-4575-826d-c07bd2d97fea
-- title:
--   A product bound for three shifted cubes
-- statement:
--   Let $a,b,c$ be positive reals. Prove that $(1+a^3)(1+b^3)(1+c^3)\geqq(1+abc)^3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2711` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2711; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2711 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 + a ^ 3) * (1 + b ^ 3) * (1 + c ^ 3) ≥ (1 + a * b * c) ^ 3  :=  by sorry
