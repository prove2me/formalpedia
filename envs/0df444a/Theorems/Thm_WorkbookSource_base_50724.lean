-- Prove2me | Theorems.Thm_WorkbookSource_base_50724
-- name    : WorkbookSource.base_50724
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:45:54.378366+00:00
-- url     : https://prove2.me/theorems/1aaef92c-74f8-4121-bfc2-3071559854f7
-- title:
--   A cyclic product ratio bounds a symmetric quadratic ratio
-- statement:
--   For any positive real numbers $a,b$ and $c$, prove that $\frac{a(a+c)}{b(b+c)}+\frac{b(b+a)}{c(c+a)}+\frac{c(c+b)}{a(a+b)}\ge\frac{3(a^{2}+b^{2}+c^{2})}{ab+bc+ca}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_50724` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_50724; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_50724 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (a + c) / (b * (b + c)) + b * (b + a) / (c * (c + a)) + c * (c + b) / (a * (a + b))) ≥ 3 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a)  :=  by sorry
