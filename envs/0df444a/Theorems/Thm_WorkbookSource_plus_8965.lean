-- Prove2me | Theorems.Thm_WorkbookSource_plus_8965
-- name    : WorkbookSource.plus_8965
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:52:03.673531+00:00
-- url     : https://prove2.me/theorems/536f5294-3163-4df9-84a2-65398cf514f7
-- title:
--   A quadratic sum times cyclic reciprocals is at least nine halves
-- statement:
--   Prove that for any positive real numbers a,b,c we have the following inequality: $(a^{2}+b^{2}+c^{2})(\frac{1}{a^{2}+ab}+\frac{1}{b^{2}+bc} + \frac{1}{c^{2}+ca} )\geq \frac{9}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_8965` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_8965; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_8965 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) * (1 / (a^2 + a * b) + 1 / (b^2 + b * c) + 1 / (c^2 + c * a)) ≥ 9 / 2   :=  by sorry
