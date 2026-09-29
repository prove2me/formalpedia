-- Prove2me | Theorems.Thm_lean_workbook_plus_2041
-- name    : lean_workbook_plus_2041
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/f19c4873-13b2-46f0-b339-e4167188c5da
-- statement:
--   There is $1$ way for the customer to select no topping at all. We will write that as $\binom{30}{0}$ . Now we will consider the number of ways that the customer can choose $1$ topping. He has $30$ toppings to choose from. We will write that as $\binom{30}{1}$ . Now, consider the number of ways that the customer can choose $2$ toppings. There are $\binom{30}{2}$ ways for that. Similarly, the number of ways to choose $3$ toppings is $\binom{30}{3}$ . Continuing in the same manner, we get $\binom{30}{4}, \binom{30}{5}, ... \binom{30}{29} + \binom{30}{30}$ , all the way up to the number of ways for $30$ toppings. Summing these up gives us $\binom{30}{0} + \binom{30}{1} + \binom{30}{2} + ... + \binom{30}{29} + \binom{30}{30} = \sum_{n = 0}^{30} \binom{30}{n}$ . This is commonly known to be equal to $2^{30}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2041 :
  ∑ k in (Finset.range 31), (Nat.choose 30 k) = 2^30   :=  by sorry
