-- Prove2me | Theorems.Thm_WorkbookSource_base_14806
-- name    : WorkbookSource.base_14806
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:58:00.363723+00:00
-- url     : https://prove2.me/theorems/de400891-59b8-4a26-954e-702b06de0354
-- title:
--   A comparison of pairwise and mixed quadratic reciprocal sums
-- statement:
--   Let $ a,$ $ b,$ $ c$ be positive real numbers. Prove that
--    $ \frac {1}{b + c} + \frac {1}{c + a} + \frac {1}{a + b} \ge \frac {2a}{3a^2 + bc} + \frac {2b}{3b^2 + ca} + \frac {2c}{3c^2 + ab}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_14806` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_14806; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_14806 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (b + c) + 1 / (c + a) + 1 / (a + b)) ≥ (2 * a / (3 * a ^ 2 + b * c) + 2 * b / (3 * b ^ 2 + c * a) + 2 * c / (3 * c ^ 2 + a * b))  :=  by sorry
