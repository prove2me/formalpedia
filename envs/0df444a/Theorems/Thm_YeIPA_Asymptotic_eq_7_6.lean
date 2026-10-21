-- Prove2me | Theorems.Thm_YeIPA_Asymptotic_eq_7_6
-- name    : YeIPA.Asymptotic.eq_7_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:38.457968+00:00
-- url     : https://prove2.me/theorems/dc6ba58c-5842-418b-aaf8-cb9d9b2033cb
-- title:
--   Relation (7.6) — on N₂(1/4) with μ ≤ μ⁰, ξ ≤ x_j ≤ 1/ξ on P* and ξ ≤ s_j ≤ 1/ξ on Z*, with ξ independent of the point
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have rank $m$, $b\in\mathbb R^m$, $c\in\mathbb R^n$, and let $(P^*,Z^*)$ be the strict complementarity partition of the standard-form pair (LP)–(LD). Let $\mu^0>0$. Then there is a number $\xi$ with $0<\xi<1$, depending only on $(A,b,c)$ and $\mu^0$, such that every $(x,y,s)\in\mathcal N_2(1/4)$ with $\mu=x^Ts/n\le\mu^0$ satisfies
--   $$\xi\le x_j\le 1/\xi\quad(j\in P^*),\qquad \xi\le s_j\le 1/\xi\quad(j\in Z^*).$$
--
--   On p. 214 the book states (7.6) for the iterates $(x^k,s^k)$ of the predictor-corrector algorithm, "where $\xi<1$ is a fixed positive quantity independent of $k$", obtained from Theorem 2.18 and relation (5.8). It is the bound on which the $O(\mu)$ estimates of Lemma 7.3 and Theorem 7.5 rest.
--
--   **Formalization Note** The book's statement is about the iterates of Algorithm 4.5, which lie in $\mathcal N_2(1/4)$ and have $\mu^k\le\mu^0=(x^0)^Ts^0/n$. Here it is stated for every point of $\mathcal N_2(1/4)$ with $\mu\le\mu^0$, which covers those iterates; the quantifier order ($\exists\xi$ before the point) is the book's "independent of $k$". The upper bounds need $\mu\le\mu^0$ (Theorem 2.18(i)); the lower bounds hold on all of $\mathcal N_2(1/4)$. The rank condition on $A$ is the book's standing assumption (stated e.g. on p. 48 and in Theorem 1.15, p. 21).
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 214, Eq. (7.6)

import Mathlib
import Definitions.Def_YeIPA_Asymptotic_LP

open Matrix

namespace YeIPA.Asymptotic

/-- Relation (7.6) (p. 214), for every point of `N₂(1/4)` with `μ ≤ μ⁰`: for LP data with
`rank A = m` and any `μ⁰ > 0` there is a constant `ξ` with `0 < ξ < 1`, depending only on
`(A, b, c)` and `μ⁰`, such that every `(x, y, s) ∈ N₂(1/4)` with `μ = xᵀs/n ≤ μ⁰` satisfies
`ξ ≤ xⱼ ≤ 1/ξ` for `j ∈ P*` and `ξ ≤ sⱼ ≤ 1/ξ` for `j ∈ Z*`. -/
theorem eq_7_6 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hA : A.rank = m) (μ0 : ℝ) (hμ0 : 0 < μ0) :
    ∃ ξ : ℝ, 0 < ξ ∧ ξ < 1 ∧
      ∀ (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ),
        InN2 A b c (1 / 4) x y s → mu x s ≤ μ0 →
          (∀ j ∈ Pstar A b c, ξ ≤ x j ∧ x j ≤ 1 / ξ) ∧
          (∀ j ∈ Zstar A b c, ξ ≤ s j ∧ s j ≤ 1 / ξ) := by sorry

end YeIPA.Asymptotic
