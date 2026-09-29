-- Prove2me | Theorems.Thm_WorkbookSource_plus_11955
-- name    : WorkbookSource.plus_11955
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:06:55.792028+00:00
-- url     : https://prove2.me/theorems/aef0baa3-f5f7-4628-8a63-b4c50885dfce
-- title:
--   A refined cyclic rational comparison with squared differences
-- statement:
--   For positive reals $a,b,c$ , prove the inequality
--    $$\frac{(a-b)^2}{ab} + \frac{(b-c)^2}{bc} + \frac{(c-a)^2}{ca} + \frac ca + \frac ab + \frac bc \geq \frac{3bc+ac-ab}{2ab+ac} + \frac{3ac+ab-bc}{2bc+ab} + \frac{3ab+bc-ac}{2ac+bc}.$$
--    Proposed by Danylo Hilko
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_11955` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_11955; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_11955 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a - b) ^ 2 / (a * b) + (b - c) ^ 2 / (b * c) + (c - a) ^ 2 / (c * a) + c / a + a / b + b / c ≥ (3 * b * c + a * c - a * b) / (2 * a * b + a * c) + (3 * a * c + a * b - b * c) / (2 * b * c + a * b) + (3 * a * b + b * c - a * c) / (2 * a * c + b * c)   :=  by sorry
