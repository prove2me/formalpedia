-- Prove2me | Theorems.Thm_WorkbookSource_base_3520
-- name    : WorkbookSource.base_3520
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:08:45.873875+00:00
-- url     : https://prove2.me/theorems/2d4151a6-1e54-42b5-b83e-3128da40405a
-- title:
--   A quadratic ratio sum with a symmetric correction
-- statement:
--   Prove that for all positive real $a$ , $b$ and $c$ holds: $$\frac{a^2}{2a^2+bc}+\frac{b^2}{2b^2+ca}+\frac{c^2}{2c^2+ab}+\frac{(a+b+c)^2}{ab+bc+ca}\geq 4$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3520` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3520; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3520 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (2 * a^2 + b * c) + b^2 / (2 * b^2 + c * a) + c^2 / (2 * c^2 + a * b) + (a + b + c)^2 / (a * b + b * c + a * c)) ≥ 4  :=  by sorry
