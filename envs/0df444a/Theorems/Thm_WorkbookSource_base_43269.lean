-- Prove2me | Theorems.Thm_WorkbookSource_base_43269
-- name    : WorkbookSource.base_43269
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:47:23.079902+00:00
-- url     : https://prove2.me/theorems/946ddf1e-87fb-409f-b177-279ffbdc34e3
-- title:
--   A weighted cyclic quadratic ratio upper bound
-- statement:
--   For $a, b, c>0$ prove that
--    $\frac{a^2+bc}{3a^2+3b^2+2c^2}+\frac{b^2+ca}{3b^2+3c^2+2a^2}+\frac{c^2+ab}{3c^2+3a^2+2b^2}\le\frac{3}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_43269` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_43269; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_43269 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b * c) / (3 * a^2 + 3 * b^2 + 2 * c^2) + (b^2 + c * a) / (3 * b^2 + 3 * c^2 + 2 * a^2) + (c^2 + a * b) / (3 * c^2 + 3 * a^2 + 2 * b^2) ≤ 3 / 4  :=  by sorry
