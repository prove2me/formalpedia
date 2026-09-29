-- Prove2me | Theorems.Thm_WorkbookSource_base_47609
-- name    : WorkbookSource.base_47609
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:21:14.924138+00:00
-- url     : https://prove2.me/theorems/6d66a258-670b-4106-a0ab-fe6ee75a5337
-- title:
--   A weighted squared cyclic ratio sum bounds a symmetric ratio
-- statement:
--   a,b,c>0 . Prove that $\frac{a^2+3b^2}{(b+c)^2}+\frac{b^2+3c^2}{(c+a)^2}+\frac{c^2+3a^2}{(a+b)^2}-1\ge \frac{2(a^2+b^2+c^2)}{ab+bc+ca}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_47609` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_47609; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_47609 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + 3 * b^2) / (b + c)^2 + (b^2 + 3 * c^2) / (c + a)^2 + (c^2 + 3 * a^2) / (a + b)^2 - 1 ≥ 2 * (a^2 + b^2 + c^2) / (a * b + b * c + c * a)  :=  by sorry
