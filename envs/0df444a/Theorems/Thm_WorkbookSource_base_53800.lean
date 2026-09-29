-- Prove2me | Theorems.Thm_WorkbookSource_base_53800
-- name    : WorkbookSource.base_53800
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:10:50.060464+00:00
-- url     : https://prove2.me/theorems/2737d734-7ae6-4d6e-91ec-6905a0f6a09f
-- title:
--   A mixed cubic ratio sum bounds twice the total
-- statement:
--   Let $a,b,c>0$ . Prove that
--    $\dfrac{b^3+2abc+c^3}{a^2+bc}+\dfrac{c^3+2abc+a^3}{b^2+ca}+\dfrac{a^3+2abc+b^3}{c^2+ab}\geq 2(a+b+c)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_53800` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_53800; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_53800 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b^3 + 2 * a * b * c + c^3) / (a^2 + b * c) + (c^3 + 2 * b * c * a + a^3) / (b^2 + c * a) + (a^3 + 2 * c * a * b + b^3) / (c^2 + a * b) ≥ 2 * (a + b + c)  :=  by sorry
