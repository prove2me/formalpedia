-- Prove2me | Theorems.Thm_YeIPA_Center_log_sum_bounds
-- name    : YeIPA.Center.log_sum_bounds
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:56:57.032425+00:00
-- url     : https://prove2.me/theorems/5c4764d3-a98c-4311-bccd-b1551c0f66b1
-- title:
--   Lemma 3.1 — $e^Td\ge\sum_i\log(1+d_i)\ge e^Td-\|d\|^2/(2(1-\|d\|_\infty))$ for $\|d\|_\infty<1$
-- statement:
--   Let $d\in\mathbb R^n$ satisfy $\|d\|_\infty=\max_i|d_i|<1$, and let $\|d\|=(\sum_i d_i^2)^{1/2}$ be its Euclidean norm. Then
--   $$e^Td\;\ge\;\sum_{i=1}^n\log(1+d_i)\;\ge\;e^Td-\frac{\|d\|^2}{2(1-\|d\|_\infty)},$$
--   where $e^Td=\sum_i d_i$.
--
--   This elementary estimate of a sum of logarithms is what turns a bound on the proximity measure $\eta(x,s)=\|Xs-e\|$ into a bound on the potential functions in Theorem 3.2 (iii) and in the potential-reduction analysis of Lemma 3.12.
--
--   **Formalization Note** $\|d\|_\infty$ is `normInf d` $=\sup_i|d_i|$ and $\|d\|^2$ is `norm2 d ^ 2` $=\sum_i d_i^2$. For $n=0$ all three quantities are $0$.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 84, Lemma 3.1

import Mathlib
import Definitions.Def_YeIPA_Center_AnalyticCenter

open Matrix

namespace YeIPA.Center

/-- Lemma 3.1 (Ye 1997, p. 84). If `d ∈ ℝⁿ` with `‖d‖_∞ < 1`, then
`eᵀd ≥ ∑ᵢ log(1 + dᵢ) ≥ eᵀd − ‖d‖² / (2(1 − ‖d‖_∞))`. -/
theorem log_sum_bounds {n : ℕ} (d : Fin n → ℝ) (hd : normInf d < 1) :
    ∑ i, Real.log (1 + d i) ≤ ∑ i, d i ∧
      ∑ i, d i - norm2 d ^ 2 / (2 * (1 - normInf d)) ≤ ∑ i, Real.log (1 + d i) := by sorry

end YeIPA.Center
