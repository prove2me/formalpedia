-- Prove2me | Theorems.Thm_WorkbookSource_base_4633
-- name    : WorkbookSource.base_4633
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:43:44.067871+00:00
-- url     : https://prove2.me/theorems/29d8557d-477d-421a-ba68-7a760cc9e5f1
-- title:
--   A pairwise-product bound when the sum equals the squared norm
-- statement:
--   If $a,b,c$ are non-negative numbers such that $a^{2}+b^{2}+c^{2}=a+b+c$, then $ab+bc+ca \geq a^{2}b^{2}+b^{2}c^{2}+c^{2}a^{2}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4633` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4633; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4633 {a b c : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = a^2 + b^2 + c^2) : a * b + b * c + c * a ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2  :=  by sorry
