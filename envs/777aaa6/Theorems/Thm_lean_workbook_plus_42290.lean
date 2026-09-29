-- Prove2me | Theorems.Thm_lean_workbook_plus_42290
-- name    : lean_workbook_plus_42290
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/f8d0f62a-6488-4a17-ba27-74f31d807f12
-- statement:
--   Let $2^k \equiv r_k \pmod{25}$ for $k\geq 0$ . The sequence $(r_k)_{k\geq 0}$ starts $1,2,4,8,16,7,\ldots$ and is periodic with period length $20$ , missing just the values $5,10,15,20$ among the integers from $1$ to $24$ . Therefore $s = \sum_{k=0}^{19} r_k = \sum_{\ell=1}^{24} \ell - (5+10+15+20) = 250$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42290 :
  ∑ k in (Finset.range 20), (2^k) % 25 = 250   :=  by sorry
