-- Prove2me | Theorems.Thm_WorkbookSource_plus_82476
-- name    : WorkbookSource.plus_82476
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:59:03.615272+00:00
-- url     : https://prove2.me/theorems/6ac59aa5-7662-4379-83fe-e054747e1255
-- title:
--   A quadratic reciprocal sum bounds a ratio of quadratic and cubic sums
-- statement:
--   Prove that
--    $\frac{a}{a^2+bc}+\frac{b}{b^2+ca}+\frac{c}{c^2+ab} \geq \frac{3(a^2+b^2+c^2)}{2(a^3+b^3+c^3)}$
--
--    Hold for positive real $a,b,c$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_82476` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_82476; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_82476 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (a ^ 2 + b * c) + b / (b ^ 2 + c * a) + c / (c ^ 2 + a * b)) ≥ 3 * (a ^ 2 + b ^ 2 + c ^ 2) / (2 * (a ^ 3 + b ^ 3 + c ^ 3))   :=  by sorry
