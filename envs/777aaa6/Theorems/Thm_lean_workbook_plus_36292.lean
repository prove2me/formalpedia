-- Prove2me | Theorems.Thm_lean_workbook_plus_36292
-- name    : lean_workbook_plus_36292
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/28fe377c-b08a-4e6a-9a12-a293f3ab72ca
-- statement:
--   Suppose $r$ pages of the book are torn off. Note that the page numbers on both the sides of a page are of the form $2k - 1$ and $2k$ , and their sum is $4k - 1.$ The sum of the numbers on the torn pages must be of the form $4k_1 - 1 + 4k_2 - 1 + .... + 4k_r - 1 = 4(k_1 + k_2 + ....+ k_r) - r.$ The sum of the numbers of all the pages in the untorn book is $1 + 2 + 3 + ... + 100 = 5050$ . Hence the sum of the numbers on the torn pages is $5050 - 4949 = 101.$ We therefore have $4(k_1 + k_2 + .... + k_r) - r = 101$ . This shows that $r$ ≡ 3 $(mod 4)$ . Thus $r = 4l + 3$ for some $l$ ≥ $0$ . Suppose $r$ ≥ $ 7$ , and suppose $k_1 < k_2 < k_3 < ... < k_r$ . Then we see that $4(k_1 + k_2 + .....+ k_r) - r$ ≥ $4(k_1 + k_2 + ..... + k_7) - 7$ ≥ $4(1 + 2 + .....+ 7) - 7$ = $4 $ × $28 - 7 = 105 > 101$ . Hence $r = 3$ . This leads to $k_1 + k_2 + k_3 = 26$ and one can choose distinct positive integers $k_1, k_2, k_3$ in several ways.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36292  (r : ℕ)
  (k : ℕ → ℕ)
  (h₀ : 0 < r ∧ 0 < k)
  (h₁ : k i < k (i + 1))
  (h₂ : ∑ i in Finset.range r, k i = 26)
  (h₃ : ∑ i in Finset.range r, (2 * k i - 1) = 101) :
  r = 3   :=  by sorry
