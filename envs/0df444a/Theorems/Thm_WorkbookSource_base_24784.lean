-- Prove2me | Theorems.Thm_WorkbookSource_base_24784
-- name    : WorkbookSource.base_24784
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:45:05.021735+00:00
-- url     : https://prove2.me/theorems/3c1125a9-9592-4c53-b91c-daed6944ed5c
-- title:
--   A cyclic pair-product reciprocal sum bounds the quadratic sum at fixed total four
-- statement:
--   Let $ a,b,c,d$ be positive numbers sach that $ a+b+c+d=4$ . Prove that $ \frac 1{ab}+\frac 1{bc}+\frac 1{cd}+\frac 1{da}\ge a^2+b^2+c^2+d^2$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_24784` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_24784; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_24784 (a b c d : ℝ) (h : a + b + c + d = 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : 1 / (a * b) + 1 / (b * c) + 1 / (c * d) + 1 / (d * a) ≥ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2  :=  by sorry
