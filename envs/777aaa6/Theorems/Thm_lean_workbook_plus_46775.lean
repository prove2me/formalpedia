-- Prove2me | Theorems.Thm_lean_workbook_plus_46775
-- name    : lean_workbook_plus_46775
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/053ae76e-e22e-4195-b061-8011caeb03f9
-- statement:
--   Now, for the second case, suppose that all four songs are liked by two people. Then we must choose which pair of people has two songs that they like, which can be done in $3$ ways. Finally, we have to assign these four songs to the pairs of people. This is given by the multinomial coefficient $\binom{4}{2, 1, 1} = \frac{4!}{2!1!1!}.$ Our total for this case is then $3\binom{4}{2, 1, 1} = 36.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46775 3 * (4! / (2! * 1! * 1!)) = 36   :=  by sorry
