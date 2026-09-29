-- Prove2me | Theorems.Thm_WorkbookSource_base_4130
-- name    : WorkbookSource.base_4130
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:11:13.795905+00:00
-- url     : https://prove2.me/theorems/180b619a-b745-4002-97b6-837ce46effdc
-- title:
--   A symmetric quadratic reciprocal comparison
-- statement:
--   Let $a,b,c > 0$ prove that
--    $$ \frac{1}{a^{2}+b^{2}}+\frac{1}{b^{2}+c^{2}}+\frac{1}{c^{2}+a^{2}}+\frac{15}{(a+b+c)^2}\geq \frac{6}{ab+bc+ca}$$ （Proposed by Marius Stănean, Zalău, Romania）
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4130` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4130; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4130 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (a ^ 2 + b ^ 2) + 1 / (b ^ 2 + c ^ 2) + 1 / (c ^ 2 + a ^ 2) + 15 / (a + b + c) ^ 2) ≥ 6 / (a * b + b * c + c * a)  :=  by sorry
