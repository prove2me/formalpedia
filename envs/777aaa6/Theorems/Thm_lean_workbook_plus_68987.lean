-- Prove2me | Theorems.Thm_lean_workbook_plus_68987
-- name    : lean_workbook_plus_68987
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/33347685-b617-4b08-a670-a6105c0e1544
-- statement:
--   For $r,n\in \mathbb {N}$ ,let $f(r,n)$ denote the number of partitions of $n$ of the form $n=n_1+n_2+...+n_s$ where ,for $i=1,2,...,s-1$ , $n_i\geq rn_{i+1}$ , and let $g(r,n)$ denote the number of partitions of $n$ ,where each part is of the form $1+r+r^2+...+r^k$ for some $k\in \mathbb {N^*}$ . Show that $ f(r,n)=g(r,n) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68987 (r n : ℕ) : (∀ s : ℕ, s > 0 ∧ n = ∑ i in Finset.range s, n_i ∧
 (∀ i : ℕ, i < s → n_i ≥ r * n_i.succ)) ↔
 (∀ s : ℕ, s > 0 ∧ n = ∑ i in Finset.range s, n_i ∧
 (∀ i : ℕ, i < s → n_i = ∑ j in Finset.range k, r^j))   :=  by sorry
