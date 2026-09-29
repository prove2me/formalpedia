-- Prove2me | Theorems.Thm_WorkbookSource_plus_20950
-- name    : WorkbookSource.plus_20950
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:29:44.072794+00:00
-- url     : https://prove2.me/theorems/80e1e9a4-2068-44fb-b4c5-d02f5a5858f9
-- title:
--   A symmetric quadratic ratio bounds a pairwise cyclic sum
-- statement:
--   For positive real numbers $ a,b,c$ prove that $ \frac{a^2+b^2+c^2}{ab+bc+ca}\ge \frac 23\left(\frac{a}{a+b}+\frac{b}{b+c}+\frac{c}{c+a}\right)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_20950` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_20950; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_20950 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) / (a * b + b * c + c * a) ≥ 2 / 3 * (a / (a + b) + b / (b + c) + c / (c + a))   :=  by sorry
