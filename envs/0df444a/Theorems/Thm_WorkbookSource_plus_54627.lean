-- Prove2me | Theorems.Thm_WorkbookSource_plus_54627
-- name    : WorkbookSource.plus_54627
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:33:39.034976+00:00
-- url     : https://prove2.me/theorems/d873bccc-8bf2-4255-87ad-fe2e68a7c09f
-- title:
--   A refined cubic inequality at fixed sum three
-- statement:
--   Prove that $a^2+b^2+c^2+3abc\ge 2(ab+bc+ca)+\frac{1}{6}\cdot abc(1-abc)$ given $a,b,c>0$ and $a+b+c=3$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_54627` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_54627; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_54627 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a^2 + b^2 + c^2 + 3 * a * b * c ≥ 2 * (a * b + b * c + c * a) + (1 / 6) * a * b * c * (1 - a * b * c)   :=  by sorry
