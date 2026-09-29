-- Prove2me | Theorems.Thm_WorkbookSource_base_22608
-- name    : WorkbookSource.base_22608
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:51:27.468994+00:00
-- url     : https://prove2.me/theorems/ea2ac212-43ac-4b22-9a01-5e963878637b
-- title:
--   A shifted quadratic ratio upper bound at fixed sum three
-- statement:
--   Let $a,b,c$ be positive real numbers such that $a+b+c=3 $. Prove that $\frac{a^2+9}{2a^2+(b+c)^2}+\frac{b^2+9}{2b^2+(c+a)^2}+\frac{c^2+9}{2c^2+(a+b)^2}\leq 5.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_22608` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_22608; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_22608 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a^2 + 9) / (2 * a^2 + (b + c)^2) + (b^2 + 9) / (2 * b^2 + (c + a)^2) + (c^2 + 9) / (2 * c^2 + (a + b)^2) ≤ 5  :=  by sorry
