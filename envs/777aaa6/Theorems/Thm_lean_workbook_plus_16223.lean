-- Prove2me | Theorems.Thm_lean_workbook_plus_16223
-- name    : lean_workbook_plus_16223
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/222a7475-f904-4239-9a31-8315b5417cbc
-- statement:
--   Assume that $S_k=\sum_{i=1}^n{x_i^k},k\in\mathbb{N},x_1,x_2,{\cdots},x_n\ge0,n\ge3$ ,then $(n-2)(n+1)(S_{k_1+k_2}+S_{k_2+k_3}+S_{k_3+k_1})-2(n-2)(S_{k_1}S_{k_2}+S_{k_2}S_{k_3}+S_{k_3}S_{k_1})+3S_{k_1+k_2+k_3}+6S_{k_1}S_{k_2}S_{k_3}-3S_{k_1+k_2}S_{k_3}-3S_{k_2+k_3}S_{k_1}-3S_{k_3+k_1}S_{k_2}+3(n-1)(n-2)\ge0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16223 (n : ℕ) (k₁ k₂ k₃ : ℕ) (x : Fin n → NNReal) : (n - 2) * (n + 1) * (∑ i, (x i) ^ (k₁ + k₂) + ∑ i, (x i) ^ (k₂ + k₃) + ∑ i, (x i) ^ (k₃ + k₁)) - 2 * (n - 2) * (∑ i, (x i) ^ k₁ * ∑ i, (x i) ^ k₂ + ∑ i, (x i) ^ k₂ * ∑ i, (x i) ^ k₃ + ∑ i, (x i) ^ k₃ * ∑ i, (x i) ^ k₁) + 3 * ∑ i, (x i) ^ (k₁ + k₂ + k₃) + 6 * (∑ i, (x i) ^ k₁) * (∑ i, (x i) ^ k₂) * (∑ i, (x i) ^ k₃) - 3 * (∑ i, (x i) ^ (k₁ + k₂)) * (∑ i, (x i) ^ k₃) - 3 * (∑ i, (x i) ^ (k₂ + k₃)) * (∑ i, (x i) ^ k₁) - 3 * (∑ i, (x i) ^ (k₃ + k₁)) * (∑ i, (x i) ^ k₂) + 3 * (n - 1) * (n - 2) ≥ 0   :=  by sorry
