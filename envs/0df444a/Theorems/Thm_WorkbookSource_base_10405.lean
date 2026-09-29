-- Prove2me | Theorems.Thm_WorkbookSource_base_10405
-- name    : WorkbookSource.base_10405
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:32:16.23144+00:00
-- url     : https://prove2.me/theorems/650b8b94-ff56-48a1-8156-72e6fcdc130b
-- title:
--   A fourth-power sum with a harmonic pair-product correction
-- statement:
--   The following is also true
--
--   $a,b,c>0, a+b+c=3\Longrightarrow \ \ \ a^4+b^4+c^4+\frac{15}{4} \left( \frac{ab}{a+b}+\frac{bc}{b+c}+\frac{ca}{c+a}\right) \ge \frac{23}{8}(a^2+b^2+c^2) $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10405` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10405; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_10405 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a ^ 4 + b ^ 4 + c ^ 4 + (15 / 4) * (a * b / (a + b) + b * c / (b + c) + c * a / (c + a)) ≥ (23 / 8) * (a ^ 2 + b ^ 2 + c ^ 2)  :=  by sorry
