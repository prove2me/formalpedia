-- Prove2me | Theorems.Thm_lean_workbook_plus_45061
-- name    : lean_workbook_plus_45061
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/8759da5a-62ed-42be-b1a1-eef3b32fddcd
-- statement:
--   The number of ways to arrange without constraints is $\dbinom{5}{3}=10$ . Then you subtract the one and only case which does not satisfy the constraints, $AAAHH$ , giving you the answer of $\boxed{9}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45061 (Nat.choose 5 3) - 1 = 9   :=  by sorry
