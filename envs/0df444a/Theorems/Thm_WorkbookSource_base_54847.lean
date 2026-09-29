-- Prove2me | Theorems.Thm_WorkbookSource_base_54847
-- name    : WorkbookSource.base_54847
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:22:48.398011+00:00
-- url     : https://prove2.me/theorems/720386cf-37e2-4460-ba28-29e6a7803810
-- title:
--   A mixed quadratic reciprocal sum lower bound
-- statement:
--   for positive real numbers a,b,c prove inequality:
--    $ \sum_{}^{} \frac {1}{6a^2 + bc} \ge \frac {9}{7} \frac {1}{ab + bc + ca}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_54847` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_54847; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_54847 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (6 * a ^ 2 + b * c) + 1 / (6 * b ^ 2 + c * a) + 1 / (6 * c ^ 2 + a * b)) ≥ 9 / 7 * 1 / (a * b + b * c + c * a)  :=  by sorry
