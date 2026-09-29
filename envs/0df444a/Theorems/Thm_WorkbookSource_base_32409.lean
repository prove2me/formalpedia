-- Prove2me | Theorems.Thm_WorkbookSource_base_32409
-- name    : WorkbookSource.base_32409
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:35:41.208973+00:00
-- url     : https://prove2.me/theorems/42864009-233d-4d75-9e41-44961326e6c2
-- title:
--   A pairwise ratio sum with a symmetric product correction
-- statement:
--   Let $a,b,c$ be positive real numbers . prove that $\frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b}+\frac{9abc}{2(a+b+c)(bc+ca+ab)}\ge 2.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_32409` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_32409; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_32409 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b) + (9 * a * b * c) / (2 * (a + b + c) * (b * c + c * a + a * b))) ≥ 2  :=  by sorry
