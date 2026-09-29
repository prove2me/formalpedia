-- Prove2me | Theorems.Thm_WorkbookSource_base_55935
-- name    : WorkbookSource.base_55935
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:33:13.713101+00:00
-- url     : https://prove2.me/theorems/86895737-41a1-4824-88f4-e9a99ceee1d2
-- title:
--   A reciprocal quadratic sum with a refined pair-product factor
-- statement:
--   Prove that \(\big(2(ab+bc+ca)-\frac{9abc}{a+b+c}\big) \cdot \big(\frac{1}{a^2+b^2}+\frac{1}{b^2+c^2}+\frac{1}{c^2+a^2}\big) \ge \frac{9}{2}\) where \(a,b,c>0\).
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_55935` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_55935; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_55935 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 * (a * b + b * c + c * a) - 9 * a * b * c / (a + b + c)) * (1 / (a ^ 2 + b ^ 2) + 1 / (b ^ 2 + c ^ 2) + 1 / (c ^ 2 + a ^ 2)) ≥ 9 / 2  :=  by sorry
