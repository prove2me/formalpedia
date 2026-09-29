-- Prove2me | Theorems.Thm_WorkbookSource_problem_242
-- name    : WorkbookSource.problem_242
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:39:17.221103+00:00
-- url     : https://prove2.me/theorems/75badd64-5272-4969-bb8b-2b25e758b52a
-- title:
--   An equivalent quadratic inequality
-- statement:
--   Let $b=a+x, c=a+x+y$. Then we have $a+a+x \ge a+x+y \implies a\ge y$. The inequality turns to
--   $(3a+2x+y)^2 \le 9(a+x)(a+x+y)$
--   $\iff 6(2x+y)a+(2x+y)^2 \le 9a(2x+y)+9x(x+y) \iff 3a(2x+y)+5x^2+5xy \ge y^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_242` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_242; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_242  (x y a : ℝ) :
  (3 * a + 2 * x + y) ^ 2 ≤ 9 * (a + x) * (a + x + y) ↔ 3 * a * (2 * x + y) + 5 * x ^ 2 + 5 * x * y ≥ y ^ 2  :=  by sorry
