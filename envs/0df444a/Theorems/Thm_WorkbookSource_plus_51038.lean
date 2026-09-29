-- Prove2me | Theorems.Thm_WorkbookSource_plus_51038
-- name    : WorkbookSource.plus_51038
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:09:32.039771+00:00
-- url     : https://prove2.me/theorems/cf040c46-aba2-4d90-8bc0-97981809b3bb
-- title:
--   Recovering a product from two power sums
-- statement:
--   From $x^2+y^2=27$ , we have $(x^2+y^2)^2=x^4+y^4+2x^2y^2=729$ and using $x^4+y^4=487$ , we have $2x^2y^2=729-487=242$ and $(xy)^2=121$ and since $x,y>0$ , we have $xy=11$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_51038` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_51038; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_51038  (x y : ℝ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x^2 + y^2 = 27)
  (h₂ : x^4 + y^4 = 487) :
  x * y = 11   :=  by sorry
