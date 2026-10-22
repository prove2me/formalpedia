-- Prove2me | Theorems.Thm_YeIPA_LP_log_sum_bounds
-- name    : YeIPA.LP.log_sum_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:57:26.108669+00:00
-- url     : https://prove2.me/theorems/286abe9c-840d-4ed0-9327-e0549c7f6fbf
-- title:
--   Lemma 3.1 — $e^Td\ge\sum\log(1+d_i)\ge e^Td-\|d\|^2/(2(1-\|d\|_\infty))$
-- statement:
--   Let $d\in\mathbb R^n$, write $\|d\|$ for its Euclidean norm and $\|d\|_\infty=\max_i|d_i|$, and suppose $\|d\|_\infty<1$. Then
--   $$e^Td\ \ge\ \sum_{i=1}^n\log(1+d_i)\ \ge\ e^Td-\frac{\|d\|^2}{2(1-\|d\|_\infty)}.$$
--
--   This scalar inequality controls the barrier term $-\sum\log x_j$ along a step, and is used in the analysis of every potential-reduction step of Chapter 4, in particular in Theorem 4.9.
--
--   **Formalization Note** This is Lemma 3.1 of Chapter 3, restated in this mission's namespace with its own `norm2` and `normInf`, because Chapter 4 uses it and the Chapter 3 mission is a separate draft. At $n=0$ all three sides are $0$.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 84, Lemma 3.1

import Mathlib
import Definitions.Def_YeIPA_LP_PotentialReduction

open Matrix

namespace YeIPA.LP

/-- Lemma 3.1 (Ye 1997, p. 84), restated for Chapter 4. If `d ∈ ℝⁿ` with `‖d‖_∞ < 1`, then
`eᵀd ≥ ∑ᵢ log(1 + dᵢ) ≥ eᵀd − ‖d‖² / (2(1 − ‖d‖_∞))`. -/
theorem log_sum_bounds {n : ℕ} (d : Fin n → ℝ) (hd : normInf d < 1) :
    ∑ i, Real.log (1 + d i) ≤ ∑ i, d i ∧
      ∑ i, d i - norm2 d ^ 2 / (2 * (1 - normInf d)) ≤ ∑ i, Real.log (1 + d i) := by sorry

end YeIPA.LP
