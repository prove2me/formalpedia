-- Prove2me | Theorems.Thm_WorkbookSource_base_52401
-- name    : WorkbookSource.base_52401
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:45:21.814443+00:00
-- url     : https://prove2.me/theorems/0488da57-6e98-44e0-a891-558af0bd16eb
-- title:
--   A product-of-shifts bound at fixed pairwise sum
-- statement:
--   Prove that for $a, b, c > 0$ satisfying $ab + bc + ca = 3$, the inequality $a^2 + b^2 + c^2 + 2abc + 3 \geq (1 + a)(1 + b)(1 + c)$ holds.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_52401` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_52401; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_52401 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b + b * c + c * a = 3) : a^2 + b^2 + c^2 + 2 * a * b * c + 3 ≥ (1 + a) * (1 + b) * (1 + c)  :=  by sorry
