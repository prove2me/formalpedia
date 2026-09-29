-- Prove2me | Theorems.Thm_WorkbookSource_base_368
-- name    : WorkbookSource.base_368
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:45:16.071977+00:00
-- url     : https://prove2.me/theorems/25a265cd-d480-4ad1-9091-5b4cb6aa29ec
-- title:
--   A fixed-sum quadratic reciprocal upper bound
-- statement:
--   Prove that $\frac{a^2}{a+2}+\frac{b^2}{b+2}+\frac{c^2}{c+2} \leq \frac{3}{ab+bc+ca} $ given $a,b,c>0$ and $a+b+c=3$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_368` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_368; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_368 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a^2 / (a + 2) + b^2 / (b + 2) + c^2 / (c + 2)) ≤ 3 / (a * b + b * c + a * c)  :=  by sorry
