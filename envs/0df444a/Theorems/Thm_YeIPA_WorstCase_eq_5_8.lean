-- Prove2me | Theorems.Thm_YeIPA_WorstCase_eq_5_8
-- name    : YeIPA.WorstCase.eq_5_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:57:34.1595+00:00
-- url     : https://prove2.me/theorems/5f4e859e-8662-4d17-8c6a-145bc9b9d9d6
-- title:
--   Display (5.8) — under property (5.7), x_jᵏ > n^{−η} x_j* ≥ n^{−η} ξ for every j ∈ P*
-- statement:
--   Let (LP) $\min\{c^Tx:Ax=b,x\ge0\}$ and (LD) $\max\{b^Ty:A^Ty+s=c,s\ge0\}$ be a standard-form pair with $n\ge1$ variables, $(P^*,Z^*)$ its strict complementarity partition, $\Omega_p$ its primal optimal face and $\xi=\xi(A,b,c)$ the condition number (5.3). Let $\eta>0$, and let $(x^k,y^k,s^k)$ be an interior point satisfying property (5.7):
--   $$\frac{\min(X^ks^k)}{(x^k)^Ts^k}>n^{-\eta}.$$
--   Then for every $j\in P^*$,
--   $$x^k_j>n^{-\eta}x^*_j\quad\text{for every }x^*\in\Omega_p,\qquad\text{and}\qquad x^k_j>n^{-\eta}\xi.$$
--
--   So along iterates that stay away from the boundary in the sense of (5.7), the coordinates in $P^*$ are bounded below by a fixed multiple of $\xi$, however small the duality gap.
--
--   **Formalization Note** Property (5.7) is `Property57 η xk sk`, written coordinatewise: $x^k_js^k_j/((x^k)^Ts^k)>n^{-\eta}$ for every $j$. Since $\min(Xs)\le x^Ts/n$, (5.7) can only hold when $n^{-\eta}<1/n$; at $n=1$ it never holds, and the statement is then vacuous, as in the book.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, pp. 154–155, proof of Theorem 5.3, display (5.8)

import Mathlib
import Definitions.Def_YeIPA_WorstCase_Termination

open Matrix

namespace YeIPA.WorstCase

/-- Display (5.8) (Ye 1997, p. 155, proof of Theorem 5.3). Let `(xᵏ, yᵏ, sᵏ)` be an interior
point of (LP)/(LD), `n ≥ 1`, satisfying property (5.7) with a constant `η > 0`, i.e.
`min(Xᵏsᵏ)/((xᵏ)ᵀsᵏ) > n^{-η}`, and let `ξ = ξ(A, b, c)`. Then for every `j ∈ P*` and every
`x* ∈ Ω_p`, `x_jᵏ > n^{-η} x_j*`, and `x_jᵏ > n^{-η} ξ`. -/
theorem eq_5_8 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hn : 0 < n) (η : ℝ) (hη : 0 < η) (xk : Fin n → ℝ) (yk : Fin m → ℝ) (sk : Fin n → ℝ)
    (hint : IsInterior A b c xk yk sk) (h57 : Property57 η xk sk)
    (j : Fin n) (hj : j ∈ Pstar A b c) :
    (∀ xs ∈ OmegaP A b c, (n : ℝ) ^ (-η) * xs j < xk j) ∧
    (n : ℝ) ^ (-η) * xi A b c < xk j := by sorry

end YeIPA.WorstCase
