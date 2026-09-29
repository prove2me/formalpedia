-- Prove2me | Theorems.Thm_WorkbookSource_problem_21933
-- name    : WorkbookSource.problem_21933
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:50:37.896381+00:00
-- url     : https://prove2.me/theorems/20758099-603b-48c4-bfad-133afba606f1
-- title:
--   Recovering a proportional quantity
-- statement:
--   $x = ay$
--   so, when $x = 4$ and $y = 8$ , we have $a = \frac{1}{2}$
--   Therefore $x = \frac{y}{2}$ and so when $y = 10$ , we get
--    $x = 5$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21933` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21933; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_21933  (x y a : ℝ)
  (h₀ : x = a * y)
  (h₁ : 4 = a * 8)
  (h₂ : y = 10) :
  x = 5  :=  by sorry
