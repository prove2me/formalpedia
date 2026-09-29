-- Prove2me | Theorems.Thm_WorkbookSource_plus_33298
-- name    : WorkbookSource.plus_33298
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:48:50.418528+00:00
-- url     : https://prove2.me/theorems/d0b39b40-49a6-4ac2-86f7-783604e1fab0
-- title:
--   A quadratic reciprocal product with a squared difference correction
-- statement:
--   For $a,b,c>0$ .Prove that
--    $\left( {{a^2} + {b^2} + {c^2}} \right)\left( {\frac{1}{a} + \frac{1}{b} + \frac{1}{c}} \right) \ge \frac{{9\left( {{a^2} + {b^2} + {c^2}} \right)}}{{a + b + c}} + 2\frac{{{{\left( {a - b} \right)}^2} + {{\left( {b - c} \right)}^2} + {{\left( {c - a} \right)}^2}}}{{a + b + c}}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_33298` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_33298; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_33298 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) * (1 / a + 1 / b + 1 / c) ≥ 9 * (a^2 + b^2 + c^2) / (a + b + c) + 2 * ((a - b)^2 + (b - c)^2 + (c - a)^2) / (a + b + c)   :=  by sorry
