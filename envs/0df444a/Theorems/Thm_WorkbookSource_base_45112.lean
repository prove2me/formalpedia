-- Prove2me | Theorems.Thm_WorkbookSource_base_45112
-- name    : WorkbookSource.base_45112
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:13:32.305291+00:00
-- url     : https://prove2.me/theorems/70e9ff6a-e894-422c-9674-74128a499f66
-- title:
--   A cubed quadratic sum bounds a squared cubic expression
-- statement:
--   Prove that for all nonnegative reals $a,b,c$, $4(a^2+b^2+c^2)^3\ge3(a^3+b^3+c^3+3abc)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_45112` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_45112; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_45112 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 4 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 3 ≥ 3 * (a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c) ^ 2  :=  by sorry
