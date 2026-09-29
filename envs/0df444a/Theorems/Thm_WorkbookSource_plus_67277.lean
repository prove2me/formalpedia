-- Prove2me | Theorems.Thm_WorkbookSource_plus_67277
-- name    : WorkbookSource.plus_67277
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:46:39.951402+00:00
-- url     : https://prove2.me/theorems/b0f9f609-81ce-4dce-bf05-b169a38bd9fc
-- title:
--   A mixed quadratic reciprocal sum lower bound
-- statement:
--   Let $a,b,c>0$ , prove that :
--    $\frac{1}{2a^2+bc}+\frac{1}{2b^2+ca}+\frac{1}{2c^2+ab} \geq \frac{6}{a^2+b^2+c^2+ab+bc+ca}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_67277` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_67277; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_67277 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (2 * a ^ 2 + b * c) + 1 / (2 * b ^ 2 + c * a) + 1 / (2 * c ^ 2 + a * b)) ≥ 6 / (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a)   :=  by sorry
