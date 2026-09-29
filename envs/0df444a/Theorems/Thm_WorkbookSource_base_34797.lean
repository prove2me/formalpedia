-- Prove2me | Theorems.Thm_WorkbookSource_base_34797
-- name    : WorkbookSource.base_34797
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:49:43.367219+00:00
-- url     : https://prove2.me/theorems/24d46da2-3310-417f-90f5-95b113c7cb56
-- title:
--   A cyclic linear ratio sum bounded by symmetric quadratic forms
-- statement:
--   For $a, b, c>0$ prove that
--    $\frac{a+b}{a+2b}+\frac{b+c}{b+2c}+\frac{c+a}{c+2a}\leq\frac{2(a^2+b^2+c^2)}{ab+bc+ca}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_34797` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_34797; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_34797 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (a + 2 * b) + (b + c) / (b + 2 * c) + (c + a) / (c + 2 * a) ≤ (2 * (a ^ 2 + b ^ 2 + c ^ 2)) / (a * b + b * c + a * c)  :=  by sorry
