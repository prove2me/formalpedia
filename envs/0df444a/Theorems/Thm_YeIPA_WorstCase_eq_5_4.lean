-- Prove2me | Theorems.Thm_YeIPA_WorstCase_eq_5_4
-- name    : YeIPA.WorstCase.eq_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:57:35.669651+00:00
-- url     : https://prove2.me/theorems/e1512fd4-9a16-44ea-8fc4-9bba5370f65d
-- title:
--   Display (5.4) — Σ_{P*} x*_i s_iᵏ + Σ_{Z*} s*_i x_iᵏ = (xᵏ)ᵀsᵏ for an interior point and a complementary optimal pair
-- statement:
--   Let (LP) $\min\{c^Tx:Ax=b,x\ge0\}$ and (LD) $\max\{b^Ty:A^Ty+s=c,s\ge0\}$ be a standard-form pair, $(P^*,Z^*)$ its strict complementarity partition and $\Omega_p$, $\Omega_d$ its optimal faces. Let $(x^k,y^k,s^k)$ be an interior point ($Ax^k=b$, $x^k>0$, $A^Ty^k+s^k=c$, $s^k>0$), and let $x^*\in\Omega_p$ and $(y^*,s^*)\in\Omega_d$. Then
--   $$(x^k-x^*)^T(s^k-s^*)=0$$
--   and
--   $$\sum_{i\in P^*}x^*_is^k_i+\sum_{i\in Z^*}s^*_ix^k_i=(x^k)^Ts^k.$$
--
--   This identity expresses the duality gap of an interior point through an optimal complementary pair; it is the first step of the proof of Theorem 5.3.
--
--   **Formalization Note** The sums are over the finsets `(Pstar A b c).toFinset` and `(Zstar A b c).toFinset`, with classical decidability.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 154, proof of Theorem 5.3, display (5.4)

import Mathlib
import Definitions.Def_YeIPA_WorstCase_Termination

open Matrix

namespace YeIPA.WorstCase

open Classical in
/-- Display (5.4) (Ye 1997, p. 154, proof of Theorem 5.3). Let `(xᵏ, yᵏ, sᵏ)` be an interior
point of (LP)/(LD) and let `x* ∈ Ω_p`, `(y*, s*) ∈ Ω_d` be a complementary pair of optimal
solutions. Since `(xᵏ − x*)ᵀ(sᵏ − s*) = 0`,
`∑_{i ∈ P*} x_i* s_iᵏ + ∑_{i ∈ Z*} s_i* x_iᵏ = (xᵏ)ᵀsᵏ`. -/
theorem eq_5_4 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (xk : Fin n → ℝ) (yk : Fin m → ℝ) (sk : Fin n → ℝ) (hint : IsInterior A b c xk yk sk)
    (xs : Fin n → ℝ) (ys : Fin m → ℝ) (ss : Fin n → ℝ)
    (hxs : xs ∈ OmegaP A b c) (hss : (ys, ss) ∈ OmegaD A b c) :
    (xk - xs) ⬝ᵥ (sk - ss) = 0 ∧
    ∑ i ∈ (Pstar A b c).toFinset, xs i * sk i + ∑ i ∈ (Zstar A b c).toFinset, ss i * xk i =
      xk ⬝ᵥ sk := by sorry

end YeIPA.WorstCase
