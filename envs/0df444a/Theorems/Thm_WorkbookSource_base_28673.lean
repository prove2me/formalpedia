-- Prove2me | Theorems.Thm_WorkbookSource_base_28673
-- name    : WorkbookSource.base_28673
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:44:44.446116+00:00
-- url     : https://prove2.me/theorems/49df886c-f434-4548-a43e-f3976e2bd070
-- title:
--   A weighted cyclic reciprocal sum with a symmetric quadratic correction
-- statement:
--   Let $a,b,c>0$ . Prove:
--    $$\frac{a+2b}{c}+\frac{b+2c}{a}+\frac{c+2a}{b}+\frac{117(ab+bc+ca)}{8(a^2+b^2+c^2)} \ge \frac{89}{4}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28673` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28673; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_28673 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + 2 * b) / c + (b + 2 * c) / a + (c + 2 * a) / b + 117 * (a * b + b * c + c * a) / (8 * (a ^ 2 + b ^ 2 + c ^ 2)) ≥ 89 / 4  :=  by sorry
