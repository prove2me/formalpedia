-- Prove2me | Theorems.Thm_lean_workbook_plus_72098
-- name    : lean_workbook_plus_72098
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/e5ea4aa7-7f54-482d-bb43-078acd853c6f
-- statement:
--   The answer is $64/195$ . In order for Bob to win, Zan must draw out all the blue chips before the red and green ones. Therefore, the problem is equivalent to calculating the probability that in a random permutation of 6 red, 7 blue and 8 green chips the last blue chip appears before at least one red and one green chip.\nSuppose there are $i\ge 1$ red chips and $j\ge 1$ blue chips after the last blue chip. Then there are $\binom{i+j}{j}$ ways to arrange those chips. Now we shall calculate the number of ways to arrange the chips before the last blue chip. Since the last blue chip is fixed (based on $i$ and $j$ ), we must find the number of ways to arrange $6-i$ red, $6$ blue and $8-j$ green chips. This is just $\binom{20-i-j}{6}\binom{14-i-j}{6-i}.$ Hence, for each $1\le i\le 6$ and $1\le j\le 8$ , there are $\binom{i+j}{j}\binom{20-i-j}{6}\binom{14-i-j}{6-i}$ ways for Bob to win. Since there are $\binom{21}{6}\binom{15}{7}$ total ways to arrange the chips, the probability Bob will win is $\frac{\sum_{j=1}^8\sum_{i=1}^6\binom{i+j}{j}\binom{20-i-j}{6}\binom{14-i-j}{6-i}}{\binom{21}{6}\binom{15}{7}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72098 :
  (∑ j in Finset.Icc 1 8, ∑ i in Finset.Icc 1 6, (Nat.choose (i + j) j * Nat.choose (20 - i - j) 6 * Nat.choose (14 - i - j) (6 - i))) / (Nat.choose 21 6 * Nat.choose 15 7) = 64 / 195   :=  by sorry
