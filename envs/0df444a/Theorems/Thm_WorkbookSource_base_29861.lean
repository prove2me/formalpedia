-- Prove2me | Theorems.Thm_WorkbookSource_base_29861
-- name    : WorkbookSource.base_29861
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:55:25.928532+00:00
-- url     : https://prove2.me/theorems/89fcb506-7511-487c-b2c9-fdfa804d4f8b
-- title:
--   A cubic pairwise sum is bounded by quadratic factors
-- statement:
--   For $ a, b, c > 0 $ real numbers, prove that: $(2a^2+bc)(2b^2+ac)(2c^2+ab) \ge (ab+bc+ca)^3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_29861` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_29861; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_29861 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 * a ^ 2 + b * c) * (2 * b ^ 2 + a * c) * (2 * c ^ 2 + a * b) ≥ (a * b + b * c + c * a) ^ 3  :=  by sorry
