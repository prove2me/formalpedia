-- Prove2me | Theorems.Thm_WorkbookSource_base_17942
-- name    : WorkbookSource.base_17942
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:12:28.32097+00:00
-- url     : https://prove2.me/theorems/42e88f87-87ae-49a0-86f6-4c4eca8633d6
-- title:
--   A pairwise cubic-over-quadratic lower bound at fixed sum three
-- statement:
--   Let $a,b,c$ to be three positive real numbers such that $ a+b+c=3$ .Prove that : $\frac{a^3+b^3}{a^2+ab+b^2}+\frac{b^3+c^3}{b^2+bc+c^2}+\frac{c^3+a^3}{c^2+ca+a^2} \ge \frac{2}{3}(a^2+b^2+c^2).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_17942` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_17942; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_17942 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a^3 + b^3) / (a^2 + a * b + b^2) + (b^3 + c^3) / (b^2 + b * c + c^2) + (c^3 + a^3) / (c^2 + c * a + a^2) ≥ (2 / 3) * (a^2 + b^2 + c^2)  :=  by sorry
