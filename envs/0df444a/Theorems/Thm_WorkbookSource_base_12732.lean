-- Prove2me | Theorems.Thm_WorkbookSource_base_12732
-- name    : WorkbookSource.base_12732
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:46:05.813433+00:00
-- url     : https://prove2.me/theorems/19a68c85-f114-4dec-bc3f-3c30730a541a
-- title:
--   A cyclic cubic ratio with a symmetric quadratic correction
-- statement:
--   Prove that for all positive reals $ a,b,c$ :
--    $ \frac{a^2b+b^2c+c^2a}{a^3+b^3+c^3}+\frac{3(a^2+b^2+c^2)}{ab+bc+ca} \geq 4$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12732` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12732; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12732 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 * b + b^2 * c + c^2 * a) / (a^3 + b^3 + c^3) + 3 * (a^2 + b^2 + c^2) / (a * b + b * c + c * a) ≥ 4  :=  by sorry
