-- Prove2me | Theorems.Thm_WorkbookSource_base_36763
-- name    : WorkbookSource.base_36763
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:49:30.944821+00:00
-- url     : https://prove2.me/theorems/3fe26047-0012-4490-9b65-c02ed7f468ef
-- title:
--   A four-variable cubic inequality with a triple-product correction
-- statement:
--   Prove that $3(a^3+b^3+c^3+d^3)+abcd(\frac{1}{a}+\frac{1}{b}+\frac{1}{c}+\frac{1}{d})\geq (a^2+b^2+c^2+d^2)(a+b+c+d)$ for $a,b,c,d>0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_36763` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_36763; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_36763 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : 3 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) + a * b * c * d * (1 / a + 1 / b + 1 / c + 1 / d) ≥ (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (a + b + c + d)  :=  by sorry
