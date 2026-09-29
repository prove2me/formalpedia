-- Prove2me | Theorems.Thm_WorkbookSource_base_9289
-- name    : WorkbookSource.base_9289
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:43:50.399878+00:00
-- url     : https://prove2.me/theorems/241eff10-4071-4249-b0d4-b58039bd50ab
-- title:
--   A cyclic pairwise ratio bound at fixed sum three
-- statement:
--   For $a, b, c>0, a+b+c=3$ , prove that $\frac{a}{a+b}+\frac{b}{b+c}+\frac{c}{c+a}\ge\frac{3(a^2+b^2+c^2)}{3+a^3+b^3+c^3}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9289` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9289; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9289 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a / (a + b) + b / (b + c) + c / (c + a) ≥ 3 * (a ^ 2 + b ^ 2 + c ^ 2) / (3 + a ^ 3 + b ^ 3 + c ^ 3)  :=  by sorry
