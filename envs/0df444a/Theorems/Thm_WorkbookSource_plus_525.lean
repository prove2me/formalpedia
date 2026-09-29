-- Prove2me | Theorems.Thm_WorkbookSource_plus_525
-- name    : WorkbookSource.plus_525
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:41:14.476385+00:00
-- url     : https://prove2.me/theorems/8edda3f6-7065-4ae5-8421-682f805695ea
-- title:
--   A work-rate equation becomes a quadratic identity
-- statement:
--   Let $ c$ be the number of days in wich worker $ C$ does his duty. So $ B$ does it in $ b + c$ and $ A$ in $ a + b + c$ days. In one day each worker, $ C$ , $ B$ and $ A$ , does respectively $ \frac {1}{c}$ , $ \frac {1}{b + c}$ and $ \frac {1}{a + b + c}$ . So if $ A$ and $ B$ together do the duty in the same time $ C$ does, we must have that: $ \frac {1}{a + b + c} + \frac {1}{b + c} = \frac {1}{c} $ Which can be reduced to $ c^2 = ab + b^2 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_525` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_525; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_525  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : 1 / (a + b + c) + 1 / (b + c) = 1 / c) :
  c^2 = a * b + b^2   :=  by sorry
