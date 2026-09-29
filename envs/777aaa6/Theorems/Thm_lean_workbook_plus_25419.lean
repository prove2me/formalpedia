-- Prove2me | Theorems.Thm_lean_workbook_plus_25419
-- name    : lean_workbook_plus_25419
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/9d04ba43-b9d8-4fae-8ca1-e539bbe08166
-- statement:
--   Consider the total number of sequences. We can express this is $2$ ways: $2^{19}$ by choosing each digit to be a $0$ or a $1$ or by writing it as $\binom{19}{0}+\binom{19}{1}+\binom{19}{2}+ \cdots + \binom{19}{19}$ . However, using the combinatorial identity $\binom{n}{k}=\binom{n}{n-k}$ on the first $10$ out of $20$ terms, we have this is equal to: \n\n $$\binom{19}{19}+\binom{19}{18}+\binom{19}{17}+\cdots+\binom{19}{17}+\binom{19}{18}+\binom{19}{19} = 2(\binom{19}{10}+\binom{19}{11}+\binom{19}{12}+ \cdots\binom{19}{18}+\binom{19}{19})$$ \n\n Thus, the sum is just $\frac{2^{19}}{2} = 2^{18}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25419 :
  ∑ k in (Finset.range 20), (Nat.choose 19 k) = 2^18   :=  by sorry
