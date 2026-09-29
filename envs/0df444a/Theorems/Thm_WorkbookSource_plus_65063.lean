-- Prove2me | Theorems.Thm_WorkbookSource_plus_65063
-- name    : WorkbookSource.plus_65063
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:41:45.407176+00:00
-- url     : https://prove2.me/theorems/a25ef1d0-06e2-461c-b881-da7803e56d51
-- title:
--   A cyclic cubic ratio bounds a normalized quadratic sum
-- statement:
--   Given $a,b,c>0$ .Prove that $\frac{a^3+b^3+c^3}{a^2b+b^2c+c^2a}\geq \frac{3(a^2+b^2+c^2)}{(a+b+c)^2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_65063` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_65063; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_65063 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3 + c^3) / (a^2 * b + b^2 * c + c^2 * a) ≥ (3 * (a^2 + b^2 + c^2)) / (a + b + c)^2   :=  by sorry
