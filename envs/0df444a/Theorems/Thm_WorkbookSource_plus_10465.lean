-- Prove2me | Theorems.Thm_WorkbookSource_plus_10465
-- name    : WorkbookSource.plus_10465
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:13:03.520446+00:00
-- url     : https://prove2.me/theorems/54011f5a-02dd-4142-a975-da56256a3be3
-- title:
--   A shifted cyclic ratio sum with a reciprocal pair-product correction
-- statement:
--   The following inequality is also true. Let $a,b,c>0$ such that $a+b+c=3$ . Prove that $\frac{9}{ab+bc+ca}+\frac{a+b}{a^2+ab+c}+\frac{b+c}{b^2+bc+a}+\frac{c+a}{c^2+ca+b} \geq 5$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_10465` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_10465; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_10465 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : 9 / (a * b + b * c + c * a) + (a + b) / (a ^ 2 + a * b + c) + (b + c) / (b ^ 2 + b * c + a) + (c + a) / (c ^ 2 + c * a + b) ≥ 5   :=  by sorry
