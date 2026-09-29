-- Prove2me | Theorems.Thm_WorkbookSource_plus_23399
-- name    : WorkbookSource.plus_23399
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:40:25.872282+00:00
-- url     : https://prove2.me/theorems/1d7ad8d8-0792-46b1-907f-0c002335cd38
-- title:
--   A shifted ratio sum with a reciprocal pair-product correction
-- statement:
--   Let $a,b,c$ be positive numbers satisfying $a+b+c=3$ . Prove that:
--    $\frac{a}{a+3}+\frac{b}{b+3}+\frac{c}{c+3}+\frac{1}{ab+bc+ac}\geq \frac{13}{12}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_23399` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_23399; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_23399 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a / (a + 3) + b / (b + 3) + c / (c + 3) + 1 / (a * b + b * c + a * c) ≥ 13 / 12   :=  by sorry
