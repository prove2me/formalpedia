-- Prove2me | Theorems.Thm_lean_workbook_plus_31265
-- name    : lean_workbook_plus_31265
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/730f3d03-0cf0-4061-9846-d8c4592d1acc
-- statement:
--   The probability of drawing RRBBGG is $\tfrac12\cdot\tfrac12\cdot\tfrac3{10}\cdot\tfrac3{10}\cdot\tfrac15\cdot\tfrac15$ . But the probability of drawing RBGRBG is exactly the same, it's just that you multiply in a different order. Because these permutations represent non-overlapping final outcomes, you can add them, so given that the number of permutations is $\tfrac{6!}{2!2!2!}$ , the total probability of drawing two of each colour is $\tfrac{6!}{2!2!2!}\cdot\tfrac12\cdot\tfrac12\cdot\tfrac3{10}\cdot\tfrac3{10}\cdot\tfrac15\cdot\tfrac15=\tfrac{81}{1000}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31265 :
  ((6! / (2! * 2! * 2!)) * (1 / 2) * (1 / 2) * (3 / 10) * (3 / 10) * (1 / 5) * (1 / 5)) = (81 / 1000)   :=  by sorry
