-- Prove2me | Theorems.Thm_YeIPA_WorstCase_eq_5_5
-- name    : YeIPA.WorstCase.eq_5_5
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:57:29.750988+00:00
-- url     : https://prove2.me/theorems/e0d69858-927c-46de-a448-9654c5eebaea
-- title:
--   Display (5.5) — for j ∈ P*, s_jᵏ ≤ (xᵏ)ᵀsᵏ / x_j*, and (xᵏ)ᵀsᵏ < ε implies s_jᵏ < ε/ξ
-- statement:
--   Let (LP) $\min\{c^Tx:Ax=b,x\ge0\}$ and (LD) $\max\{b^Ty:A^Ty+s=c,s\ge0\}$ be a standard-form pair with $n\ge1$ variables, $(P^*,Z^*)$ its strict complementarity partition, $\Omega_p$ its primal optimal face and $\xi=\xi(A,b,c)$ the condition number (5.3). Let $(x^k,y^k,s^k)$ be an interior point and $j\in P^*$. Then
--
--   1. for every $x^*\in\Omega_p$ with $x^*_j>0$,
--   $$s^k_j\le\frac{(x^k)^Ts^k}{x^*_j};$$
--   2. for every $\epsilon$, if $(x^k)^Ts^k<\epsilon$ then
--   $$s^k_j<\epsilon/\xi.$$
--
--   In words: on the indices of $P^*$, the dual slacks of an interior point are at most the duality gap divided by $\xi$.
--
--   **Formalization Note** The book takes $x^*$ maximizing $x_j$ on $\Omega_p$; part 1 is stated for every $x^*\in\Omega_p$ with $x^*_j>0$, and part 2 is the book's conclusion with the bound $\epsilon/\xi$.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 154, proof of Theorem 5.3, display (5.5)

import Mathlib
import Definitions.Def_YeIPA_WorstCase_Termination

open Matrix

namespace YeIPA.WorstCase

/-- Display (5.5) (Ye 1997, p. 154, proof of Theorem 5.3). Let `(xᵏ, yᵏ, sᵏ)` be an interior
point of (LP)/(LD), `n ≥ 1`, `ξ = ξ(A, b, c)` and `j ∈ P*`. For every `x* ∈ Ω_p` with
`x_j* > 0`, `s_jᵏ ≤ (xᵏ)ᵀsᵏ / x_j*`; and if `(xᵏ)ᵀsᵏ < ε` then `s_jᵏ < ε / ξ`. -/
theorem eq_5_5 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hn : 0 < n) (xk : Fin n → ℝ) (yk : Fin m → ℝ) (sk : Fin n → ℝ)
    (hint : IsInterior A b c xk yk sk) (j : Fin n) (hj : j ∈ Pstar A b c) :
    (∀ xs ∈ OmegaP A b c, 0 < xs j → sk j ≤ xk ⬝ᵥ sk / xs j) ∧
    ∀ ε : ℝ, xk ⬝ᵥ sk < ε → sk j < ε / xi A b c := by sorry

end YeIPA.WorstCase
