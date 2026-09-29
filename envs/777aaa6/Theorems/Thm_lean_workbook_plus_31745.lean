-- Prove2me | Theorems.Thm_lean_workbook_plus_31745
-- name    : lean_workbook_plus_31745
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/9c8499bb-ac7e-4670-8b64-5ed9d87e958b
-- statement:
--   Find all triples of integer $(m,n,k)$ such that : \n $3^m+2^n+2015=(3k)!$ \n Clearly $m,n,k\ge 0$ . Since $3^m+2^n+2015=(3k)!>2015$ , we have $k\ge 3$ . If $m\ge 2$ , then $ 2^n\equiv -2015\equiv 1\pmod {9}$ , so $n=6t$ for some $t\ge 0$ , but then $2^n\equiv 1\pmod{7}$ , so $7\mid 3^m$ , contradiction. \n \n If $m=1$ , then $2^n+2018=(3k)!$ . If $n\ge 2$ , then contradiction mod $4$ . If $n\in\{0,1\}$ , no solutions. \n \n If $m=0$ , then $2^n+2016=(3k)!$ , contradiction mod $3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31745  (m n k : ℕ)
  (h₀ : 0 ≤ m ∧ 0 ≤ n ∧ 0 ≤ k)
  (h₁ : (3^m + 2^n + 2015) = (3 * k)! ) :
  m = 0 ∧ n = 2 ∧ k = 3   :=  by sorry
