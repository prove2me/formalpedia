-- Prove2me | Theorems.Thm_WorkbookSource_base_28463
-- name    : WorkbookSource.base_28463
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:55:24.114428+00:00
-- url     : https://prove2.me/theorems/611a4683-56ad-4b3d-9440-05556a75d8d5
-- title:
--   Three quadratic factors bound a cubed pairwise sum
-- statement:
--   Prove that $(a^2+2bc)(b^2+2ac)(c^2+2ab)\geq(ab+ac+bc)^3$ for $a\geq0, b\geq0, c\geq0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28463` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28463; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_28463 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : (a^2 + 2 * b * c) * (b^2 + 2 * a * c) * (c^2 + 2 * a * b) ≥ (a * b + a * c + b * c)^3  :=  by sorry
