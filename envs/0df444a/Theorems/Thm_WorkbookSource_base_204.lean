-- Prove2me | Theorems.Thm_WorkbookSource_base_204
-- name    : WorkbookSource.base_204
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:44:05.3519+00:00
-- url     : https://prove2.me/theorems/ce632a8f-aeef-4670-8455-a47dfb00a342
-- title:
--   A cubic refinement of the sum of pairwise ratios
-- statement:
--   Given that $ a,b,c$ are positive reals, prove that:
--
--   b)
--    $ \frac {a}{b + c} + \frac {b}{c + a} + \frac {c}{a + b} \geq \frac {a^3 + b^3 + c^3 + 3abc}{a^2(b + c) + b^2(c + a) + c^2(a + b)} + \frac {1}{2} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_204` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_204; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_204 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b)) ≥ (a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c) / (a ^ 2 * (b + c) + b ^ 2 * (c + a) + c ^ 2 * (a + b)) + 1 / 2  :=  by sorry
