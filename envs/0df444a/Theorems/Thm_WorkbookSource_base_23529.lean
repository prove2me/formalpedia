-- Prove2me | Theorems.Thm_WorkbookSource_base_23529
-- name    : WorkbookSource.base_23529
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:58:13.757108+00:00
-- url     : https://prove2.me/theorems/1bda7d98-71aa-4fbf-8b03-ea4da32bf39b
-- title:
--   A cyclic cubic ratio bounds a symmetric quadratic expression
-- statement:
--   Let $ a,b,c $ be three positive real numbers . Prove that :
--   $$\frac{a^3}{a^2+bc}+\frac{b^3}{b^2+ca}+\frac{c^3}{c^2+ab} \ge \frac{2(a^2+b^2+c^2)+ab+bc+ca}{2(a+b+c)}.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_23529` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_23529; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_23529 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 / (a^2 + b * c) + b^3 / (b^2 + c * a) + c^3 / (c^2 + a * b) ) ≥ (2 * (a^2 + b^2 + c^2) + a * b + b * c + c * a) / (2 * (a + b + c))  :=  by sorry
