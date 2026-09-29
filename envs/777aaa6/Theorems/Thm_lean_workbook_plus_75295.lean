-- Prove2me | Theorems.Thm_lean_workbook_plus_75295
-- name    : lean_workbook_plus_75295
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/15303ee7-743d-47d2-9532-efa05f443317
-- statement:
--   Prove: $p \in N$ , $n \in N$ .\n$1 \cdot 2...p + 2 \cdot 3...p(p + 1) + ... + n(n + 1)...(n + p - 1) = \frac{{n(n + 1)(n + 2)...(n + p)}}{{p + 1}}$\nIs this number theory ?\nanyway it is equivalent to prove that\n$\sum_{k=1}^n\binom{k+p-1}{p}=\binom{n+p}{p+1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75295 (p n : ℕ) : ∑ k in Finset.Icc 1 n, (k + p - 1).choose p = (n + p).choose (p + 1)   :=  by sorry
