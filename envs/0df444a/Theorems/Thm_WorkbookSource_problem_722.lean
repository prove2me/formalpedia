-- Prove2me | Theorems.Thm_WorkbookSource_problem_722
-- name    : WorkbookSource.problem_722
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:39:12.430912+00:00
-- url     : https://prove2.me/theorems/83f6e56c-5976-4286-a481-061c2e842ce3
-- title:
--   A weighted quadratic inequality
-- statement:
--   By AM-GM, $16x^2+25y^2+36z^2=\frac{45}{2}(y^2+z^2)+\frac{27}{2}(z^2+x^2)+\frac{5}{2}(x^2+y^2)\ge 45yz+27xz+5xy .$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_722` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_722; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_722 : ∀ x y z : ℝ, 16 * x ^ 2 + 25 * y ^ 2 + 36 * z ^ 2 ≥ 45 * y * z + 27 * z * x + 5 * x * y  :=  by sorry
