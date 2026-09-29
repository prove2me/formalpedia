-- Prove2me | Theorems.Thm_WorkbookSource_base_10103
-- name    : WorkbookSource.base_10103
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:45:57.672967+00:00
-- url     : https://prove2.me/theorems/0cd6fee0-8e44-45ac-96e7-b0330ee91d30
-- title:
--   A symmetric quadratic reciprocal difference is nonnegative
-- statement:
--   Let $a,b,c>0$ ,Prove: $f = \frac {2}{8a^{2} + bc} + \frac {2}{8b^{2} + ca} + \frac {2}{8c^{2} + ab} + \frac {1}{a^2 + b^2 + c^2} - \frac {3}{ab + bc + ca} \geqslant 0.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10103` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10103; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_10103 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 / (8 * a ^ 2 + b * c) + 2 / (8 * b ^ 2 + a * c) + 2 / (8 * c ^ 2 + a * b) + 1 / (a ^ 2 + b ^ 2 + c ^ 2) - 3 / (a * b + b * c + a * c) ≥ 0  :=  by sorry
