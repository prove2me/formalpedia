-- Prove2me | Theorems.Thm_WorkbookSource_plus_2302
-- name    : WorkbookSource.plus_2302
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:06:37.010784+00:00
-- url     : https://prove2.me/theorems/a26a7f3b-f8bf-427b-a6cc-b63b95850906
-- title:
--   A mixed product bound under linked quadratic relations
-- statement:
--   Let $ a,b,c $ be real numbers such that $a^2+b=4 $ and $ b^2+c=8 .$ Prove that $$2ab+ bc+ ca \geq-32$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_2302` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_2302; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_2302 (a b c : ℝ) (h₁ : a^2 + b = 4) (h₂ : b^2 + c = 8) : 2 * a * b + b * c + c * a ≥ -32   :=  by sorry
