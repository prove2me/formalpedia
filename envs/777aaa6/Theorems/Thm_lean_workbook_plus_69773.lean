-- Prove2me | Theorems.Thm_lean_workbook_plus_69773
-- name    : lean_workbook_plus_69773
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/b46ceb57-fc58-414c-b3ff-bfc48f821979
-- statement:
--   We can calculate each case (with 10, 11, 12, 13, ... 19 1s) as: \n\n $\binom{18}{9} + \binom{18}{10} + \binom{18}{11} + \dots + \binom{18}{18}$ . We subtract 1 because we must have 1 as the leading digit. We proceed by binomial identities. $\binom{18}{9} + \binom{18}{10} + \binom{18}{11} + \dots + \binom{18}{18} = \frac{1}{2}(2^{18} - \binom{18}{9}) = \boxed{106762}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69773 : ∑ k in (Finset.Icc 9 18), Nat.choose 18 k = 106762   :=  by sorry
