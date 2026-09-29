-- Prove2me | Theorems.Thm_WorkbookSource_problem_51665
-- name    : WorkbookSource.problem_51665
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:09:04.981793+00:00
-- url     : https://prove2.me/theorems/f54d7de5-58be-4e37-9648-8d4bd787d757
-- title:
--   A sixth-degree inequality above one
-- statement:
--   We must consider two subcases:
--   a) $a \ge 1$
--   Let $a=1+t$ we should prove: $3t^2+20t^4+12t^5+2t^6\ge 0$ ,which is obvious.
--   b) $a< 1$
--   Let $a=1/x$ with $x>1$ .We should prove that: $11x^3+2x^6+2\ge 10x^2+5x^5$ (\*).Let $x=1+p$ , $p>0$ .(\*) is equivalent to :
--    $3p^2+p^3+5p^4+7p^5+2p^6 \ge 0$ ,which is obvious.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_51665` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_51665; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_51665  (x : ℝ)
  (h₀ : 1 < x) :
  11 * x^3 + 2 * x^6 + 2 ≥ 10 * x^2 + 5 * x^5  :=  by sorry
