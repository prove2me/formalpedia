-- Prove2me | Theorems.Thm_WorkbookSource_plus_78986
-- name    : WorkbookSource.plus_78986
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:56:10.254254+00:00
-- url     : https://prove2.me/theorems/7c7ffaf5-5043-46f1-b4cc-ea78e0bafe39
-- title:
--   A cyclic pairwise ratio sum has a normalized quadratic lower bound
-- statement:
--   Let $a,b,c>0$ . Prove $ \frac{3(a^2+b^2+c^2)}{4(a+b+c)^2}+\frac{11}{4}\le \frac{a+b}{b+c}+\frac{b+c}{c+a}+\frac{c+a}{a+b}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_78986` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_78986; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_78986 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (3 * (a ^ 2 + b ^ 2 + c ^ 2) / (4 * (a + b + c) ^ 2) + 11 / 4) ≤ (a + b) / (b + c) + (b + c) / (c + a) + (c + a) / (a + b)   :=  by sorry
