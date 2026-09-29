-- Prove2me | Theorems.Thm_lean_workbook_plus_22380
-- name    : lean_workbook_plus_22380
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/c69a7caf-5f79-47a7-ac37-d937322485bb
-- statement:
--   If $a_1,a_2,\dots,a_n$ are nonnegative integers let $f(1)$ denotes the number of them that are greater than or equal to 1, $f(2)$ the number greater than or equal to 2, etc. Then $a_1+a_2+\cdots +a_n = f(1) + f(2) + f(3) + \cdots$ since $a_i$ contributes 1 to each of the numbers $f(1),f(2),\dots,f(a_i)$ . For $1\leq j\leq n$ , let $a_j$ be the largest integer such that $p^{a_j}|j$ . Then we see that $e=a_1+a_2+\cdots +a_n$ . Also $f(1)$ counts the number of integers $\leq n$ that are divisible by $p$ , $f(2)$ the number divisible by $p^2$ etc. so $f(k)$ counts the integers $p^k,2p^k,3p^k,\dots,\lfloor {n}/{p^k}\rfloor p^k$ , so that $f(k)=\lfloor n/p^k\rfloor$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22380 (p n e : ℕ) (hp : 1 < p) (hp1 : p.Prime) (hpe : e = ∑ k in Finset.Icc 1 n, (Nat.floor (n/(p^k)))) : e = ∑ k in Finset.Icc 1 n, (Nat.floor (n/(p^k)))   :=  by sorry
