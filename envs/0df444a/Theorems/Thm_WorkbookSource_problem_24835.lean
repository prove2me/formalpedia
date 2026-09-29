-- Prove2me | Theorems.Thm_WorkbookSource_problem_24835
-- name    : WorkbookSource.problem_24835
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:36:45.326587+00:00
-- url     : https://prove2.me/theorems/fbcd794a-1839-4185-9f55-2888f54c3a8d
-- title:
--   The product of two nine-digit integers
-- statement:
--   Now,
--    \begin{align*} 123456789 \cdot 987654321 &= \left(\dfrac{10^{10} - 91}{81}\right)\left(\dfrac{8 \cdot 10^{10} + 1}{81}\right) \ &= \dfrac{8 \cdot 10^{20} + 10^{10} - 728 \cdot 10^{10} - 91}{81^2} \end{align*}
--    The numerator can be easily calculated with some addition and subtraction. We get:
--    \begin{align*} 123456789 \cdot 987654321 &= \dfrac{8 \cdot 10^{20} + 10^{10} - 728 \cdot 10^{10} - 91}{6561} \ &= \dfrac{799 999 992 729 999 999 909}{6561} \end{align*}
--    Long division isn't too tedious, calculating gives:
--    $123456789 \cdot 987654321 = 121932631112635269$ and we are done.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_24835` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_24835; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_24835  (q e : ℕ)
  (h₀ : q = 123456789 * 987654321)
  (h₁ : e = 121932631112635269) :
  q = e  :=  by sorry
