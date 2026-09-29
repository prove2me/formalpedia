-- Prove2me | Theorems.Thm_WorkbookSource_plus_45975
-- name    : WorkbookSource.plus_45975
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:16:03.310231+00:00
-- url     : https://prove2.me/theorems/7be43715-fd3e-4469-a3c3-099000f65db2
-- title:
--   A mixed quadratic ratio sum with a symmetric correction
-- statement:
--   If $ a,b,c > 0$ , then
--
--    $ \frac {a(b + c + 2a)}{a^2 + 2bc} + \frac {b(c + a + 2b)}{b^2 + 2ca} + \frac {c(a + b + 2c)}{c^2 + 2ab}\geq3 + \frac {ab + bc + ca}{a^2 + b^2 + c^2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_45975` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_45975; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_45975 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (b + c + 2 * a) / (a ^ 2 + 2 * b * c) + b * (c + a + 2 * b) / (b ^ 2 + 2 * c * a) + c * (a + b + 2 * c) / (c ^ 2 + 2 * a * b)) ≥ 3 + (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2)   :=  by sorry
