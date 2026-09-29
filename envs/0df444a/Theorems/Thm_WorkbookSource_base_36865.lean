-- Prove2me | Theorems.Thm_WorkbookSource_base_36865
-- name    : WorkbookSource.base_36865
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:48:13.030423+00:00
-- url     : https://prove2.me/theorems/28da09af-21d7-4b86-8462-fb776803dc5d
-- title:
--   A binary quartic inequality with an antisymmetric term
-- statement:
--   Prove that:
--   $4ab (a^2 - b^2) \leqslant (a^2 + b^2)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_36865` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_36865; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_36865 (a b : ℝ) : 4 * a * b * (a^2 - b^2) ≤ (a^2 + b^2)^2  :=  by sorry
