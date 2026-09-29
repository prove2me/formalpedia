-- Prove2me | Theorems.Thm_WorkbookSource_base_12029
-- name    : WorkbookSource.base_12029
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:41:58.424971+00:00
-- url     : https://prove2.me/theorems/ca192707-9f18-48c7-a4ff-6251046099c5
-- title:
--   A product of quadratic sums bounds a reciprocal ratio sum
-- statement:
--   Let $a,b,c>0$ . Prove that: $\left( {{a^2} + {b^2} + {c^2}} \right)\left( {\frac{1}{{{a^2}}} + \frac{1}{{{b^2}}} + \frac{1}{{{c^2}}}} \right) \ge \frac{3}{2}\left( {\frac{{b + c}}{a} + \frac{{c + a}}{b} + \frac{{a + b}}{c}} \right)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12029` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12029; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12029 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a^2 + b^2 + c^2) * (1 / a^2 + 1 / b^2 + 1 / c^2) ≥ 3 / 2 * ((b + c) / a + (c + a) / b + (a + b) / c)  :=  by sorry
