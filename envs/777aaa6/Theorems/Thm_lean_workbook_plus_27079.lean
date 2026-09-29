-- Prove2me | Theorems.Thm_lean_workbook_plus_27079
-- name    : lean_workbook_plus_27079
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/5f6dd885-863e-4d6a-a425-eafb20c77264
-- statement:
--   Using the hockey-stick identity, $\frac{1*^{n-1}C_{k-1}+2*^{n-2}C_{k-1}+...+(n-k+1)*^{k-1}C_{k-1}}{^nC_k}=\frac{^nC_k+1*^{n-2}C_{k-1}+2*^{n-3}C_{k-1}+...+(n-k)*^{k-1}C_{k-1}}{^nC_k}=\frac{^nC_k+^{n-1}C_k+1*^{n-3}C_{k-1}...+(n-k-1)*^{k-1}C_{k-1}}{^nC_k}=...=\frac{^nC_k+^{n-1}C_k+...+^{k+1}C_k+^{k-1}C_{k-1}}{^nC_k}=\frac{^nC_k+^{n-1}C_k+...+^{k+1}C_k+^kC_k}{^nC_k}=\frac{^{n+1}C_{k+1}}{^nC_k}=\frac{(n+1)!}{(k+1)!}\frac{k!}{n!}=\frac{n+1}{k+1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27079 : ∀ n k : ℕ, n > k → (∑ i in Finset.Icc 1 (n - k + 1), (i + 1) * choose (n - i) (k - 1)) / choose n k = (n + 1) / (k + 1)   :=  by sorry
