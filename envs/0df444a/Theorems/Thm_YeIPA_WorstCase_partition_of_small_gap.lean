-- Prove2me | Theorems.Thm_YeIPA_WorstCase_partition_of_small_gap
-- name    : YeIPA.WorstCase.partition_of_small_gap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:57:41.860312+00:00
-- url     : https://prove2.me/theorems/67675821-a706-4d71-b3ac-738863752c43
-- title:
--   Proof of Theorem 5.3, p. 155 — if (5.7) holds and (xᵏ)ᵀsᵏ ≤ n^{−η}ξ², then σᵏ = P*
-- statement:
--   Let (LP) $\min\{c^Tx:Ax=b,x\ge0\}$ and (LD) $\max\{b^Ty:A^Ty+s=c,s\ge0\}$ be a standard-form pair with $n\ge1$ variables, $(P^*,Z^*)$ its strict complementarity partition and $\xi=\xi(A,b,c)$ the condition number (5.3). Let $\eta>0$, and let $(x^k,y^k,s^k)$ be an interior point satisfying property (5.7), $\min(X^ks^k)/((x^k)^Ts^k)>n^{-\eta}$. If
--   $$(x^k)^Ts^k\le n^{-\eta}\xi^2,$$
--   then $s^k_j<x^k_j$ for every $j\in P^*$, $x^k_j<s^k_j$ for every $j\in Z^*$, and consequently
--   $$\sigma^k=\{j: x^k_j\ge s^k_j\}=P^*.$$
--
--   This is the deterministic core of Theorem 5.3: once the duality gap of a well-centered interior point falls below $n^{-\eta}\xi^2$, comparing $x^k_j$ with $s^k_j$ identifies the strict complementarity partition exactly.
--
--   **Formalization Note** Property (5.7) is written coordinatewise, as in the definition module. The threshold $n^{-\eta}\xi^2$ is the book's $\epsilon$ in the final display of the proof.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 155, proof of Theorem 5.3

import Mathlib
import Definitions.Def_YeIPA_WorstCase_Termination

open Matrix

namespace YeIPA.WorstCase

/-- Proof of Theorem 5.3 (Ye 1997, pp. 154–155), the deterministic core. Let `(xᵏ, yᵏ, sᵏ)` be
an interior point of (LP)/(LD), `n ≥ 1`, satisfying property (5.7) with a constant `η > 0`,
and let `ξ = ξ(A, b, c)`. If `(xᵏ)ᵀsᵏ ≤ n^{-η} ξ²`, then `s_jᵏ < x_jᵏ` for every `j ∈ P*`,
`x_jᵏ < s_jᵏ` for every `j ∈ Z*`, and `σᵏ = {j : x_jᵏ ≥ s_jᵏ} = P*`. -/
theorem partition_of_small_gap {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hn : 0 < n) (η : ℝ) (hη : 0 < η)
    (xk : Fin n → ℝ) (yk : Fin m → ℝ) (sk : Fin n → ℝ)
    (hint : IsInterior A b c xk yk sk) (h57 : Property57 η xk sk)
    (hgap : xk ⬝ᵥ sk ≤ (n : ℝ) ^ (-η) * xi A b c ^ 2) :
    (∀ j ∈ Pstar A b c, sk j < xk j) ∧ (∀ j ∈ Zstar A b c, xk j < sk j) ∧
    sigma xk sk = Pstar A b c := by sorry

end YeIPA.WorstCase
