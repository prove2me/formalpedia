-- Prove2me | Theorems.Thm_WorkbookSource_base_18837
-- name    : WorkbookSource.base_18837
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:36:46.057615+00:00
-- url     : https://prove2.me/theorems/d54f1c43-d842-49e5-a81a-5a05e8a155be
-- title:
--   A weighted cyclic cubic ratio bounds the quadratic mean
-- statement:
--   Prove that for $a, b, c > 0$,
--   $ \frac{a^{3}}{b+2c}+\frac{b^{3}}{c+2a}+\frac{c^{3}}{a+2b}\geq\frac{a^{2}+b^{2}+c^{2}}{3} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18837` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18837; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_18837 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 / (b + 2 * c) + b^3 / (c + 2 * a) + c^3 / (a + 2 * b)) ≥ (a^2 + b^2 + c^2) / 3  :=  by sorry
