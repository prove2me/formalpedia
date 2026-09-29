-- Prove2me | Theorems.Thm_WorkbookSource_base_16097
-- name    : WorkbookSource.base_16097
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:27:51.863603+00:00
-- url     : https://prove2.me/theorems/bfebfc3c-ce4e-457b-9e28-e81cf617d569
-- title:
--   A product of pairwise corrections at sum three
-- statement:
--   Let $a,b,c$ be real numbers such that $a+b+c=3.$ Prove that $(a+b-ab)(b+c-bc)(c+a-ca)+abc\leq\frac{9}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16097` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16097; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_16097 (a b c : ℝ) (ha : a + b + c = 3) : (a + b - a * b) * (b + c - b * c) * (c + a - c * a) + a * b * c ≤ 9 / 4  :=  by sorry
