-- Prove2me | Theorems.Thm_lean_workbook_plus_11120
-- name    : lean_workbook_plus_11120
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/5f910e32-df16-4697-ab62-7c448e947996
-- statement:
--   Let $a\notin\mathbb Q$ , $u\in(0,1)$ and $\epsilon\in(0,\min(u,1-u))$ so that $(u-\epsilon,u+\epsilon)\subset (0,1)$\nLet $\frac{h_n}{k_n}$ be the successive convergents of $a$ (in its continued fraction development). \n$\forall n$ even, We have $0<x-\frac{h_n}{k_n}<\frac 1{k_nk_{n+1}}$ and so $k_nx=h_n+y_n$ with $0<y_n<\frac 1{k_{n+1}}$\nSo we can choose even $n$ such that $0<y_n<\frac 1{k_{n+1}}<\epsilon$ and then choose $m$ such that $my_n\in(u-\epsilon, u+\epsilon)$ and so $\{mk_nx\}\in(u-\epsilon,u+\epsilon)$\nSo any $u\in(0,1)$ is an accumulation point of $\left\{\{na\}\right\}_{n\in\mathbb N}$ .\nHence the required result : $\left\{\{na\}\right\}_{n\in\mathbb N}$ is dense in $[0,1]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11120 (a : ℝ) (ha : a ∉ Set.range ((↑) : ℚ → ℝ)) :
   DenseRange (λ n : ℕ => (↑n * a) % 1)   :=  by sorry
