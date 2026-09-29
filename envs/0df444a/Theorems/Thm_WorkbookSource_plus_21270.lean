-- Prove2me | Theorems.Thm_WorkbookSource_plus_21270
-- name    : WorkbookSource.plus_21270
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:09:20.501668+00:00
-- url     : https://prove2.me/theorems/c9a53e88-992e-43ef-ab99-f5006eabf2c0
-- title:
--   The square function is not injective
-- statement:
--   Function $f(x)=x^2$ is not one-one
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_21270` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_21270; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_21270 (f : ℝ → ℝ) (h₁ : ∀ x, f x = x^2) : ¬ (∀ x y, f x = f y → x = y)   :=  by sorry
