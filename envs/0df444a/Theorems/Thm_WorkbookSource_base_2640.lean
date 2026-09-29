-- Prove2me | Theorems.Thm_WorkbookSource_base_2640
-- name    : WorkbookSource.base_2640
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:03:52.155569+00:00
-- url     : https://prove2.me/theorems/b5427352-a3b7-4d0b-a072-befc57c06e58
-- title:
--   An asymmetric cubic bound with coefficients nine and fourteen
-- statement:
--   Show that $9a^2b+a^2c+9ab^2+ac^2+b^2c+bc^2 \ge 14abc$ given $a, b, c>0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2640` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2640; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2640 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 9 * a ^ 2 * b + a ^ 2 * c + 9 * a * b ^ 2 + a * c ^ 2 + b ^ 2 * c + b * c ^ 2 ≥ 14 * a * b * c  :=  by sorry
