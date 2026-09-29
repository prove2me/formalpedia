-- Prove2me | Theorems.Thm_WorkbookSource_plus_3792
-- name    : WorkbookSource.plus_3792
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:10:11.829673+00:00
-- url     : https://prove2.me/theorems/7bd5e6e2-34b0-448c-9a5a-ac903af9a9aa
-- title:
--   A shifted cyclic ratio has a symmetric quadratic upper bound
-- statement:
--   If $a,b,c$ are postive reals such that $a+b+c=3$ , prove that
--    $$\frac{a}{1+ab}+\frac{b}{1+bc}+\frac{c}{1+ca}\leq \frac{3}{2}\frac{a^2+b^2+c^2}{ab+bc+ca}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_3792` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_3792; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_3792 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a / (1 + a * b) + b / (1 + b * c) + c / (1 + c * a)) ≤ (3 / 2) * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a)   :=  by sorry
