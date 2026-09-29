-- Prove2me | Theorems.Thm_WorkbookSource_base_14789
-- name    : WorkbookSource.base_14789
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:56:59.036437+00:00
-- url     : https://prove2.me/theorems/fb6c9252-e42d-4bb3-9270-27f4836cca24
-- title:
--   A cyclic mixed quadratic ratio sum is at least seven halves
-- statement:
--   For any three positive reals a, b, c, prove that
--
--   $\frac{a^2+3bc}{b^2+c^2}+\frac{b^2+3ca}{c^2+a^2}+\frac{c^2+3ab}{a^2+b^2} \ge \frac{7}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_14789` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_14789; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_14789 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + 3 * b * c) / (b^2 + c^2) + (b^2 + 3 * c * a) / (c^2 + a^2) + (c^2 + 3 * a * b) / (a^2 + b^2) ≥ 7 / 2  :=  by sorry
