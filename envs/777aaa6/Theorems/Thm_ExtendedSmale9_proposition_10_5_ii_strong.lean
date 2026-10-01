-- Prove2me | Theorems.Thm_ExtendedSmale9_proposition_10_5_ii_strong
-- name    : ExtendedSmale9.proposition_10_5_ii_strong
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T15:46:05.72498+00:00
-- url     : https://prove2.me/theorems/bc43217a-8e3c-4b6a-a67c-efbfc2c90d0b
-- title:
--   Proposition 10.5 (ii), deterministic part — $\varepsilon_B^s\ge\kappa/2$ under (a)–(c)
-- statement:
--   Let $\{\Xi,\Omega,M,\Lambda\}$ be a computational problem with a countable evaluation family $\Lambda=\{\Lambda_k\}$, and let $(\iota^1_n)_{n\ge1}$, $(\iota^2_n)_{n\ge1}$ be sequences in $\Omega$. Suppose
--
--   - **(a)** there are $S^1,S^2\subseteq M$ and $\kappa>0$ with $d(x_1,x_2)\ge\kappa$ for all $x_1\in S^1$, $x_2\in S^2$, and $\Xi(\iota^j_n)\subseteq S^j$ for $j=1,2$;
--   - **(b)–(c)** there is $\iota^0\in\Omega$ with $|\Lambda_k(\iota^j_n)-\Lambda_k(\iota^0)|\le 4^{-n}$ for all $k$, $j=1,2$ and $n\ge1$.
--
--   Then there exists $\hat\Lambda\in L^1(\Lambda)$ such that the problem $\{\Xi,\Omega,M,\hat\Lambda\}$ satisfies $\varepsilon_B^s\ge\kappa/2$. This is the deterministic part of claim (ii) of Proposition 10.5. The probabilistic inequalities are not included.
-- source:
--   A. Bastounis, A. C. Hansen, V. Vlačić, *The extended Smale's 9th problem — On computational barriers and paradoxes in estimation, regularisation, computer-assisted proofs, and learning* (preprint, 126 pp., version of 28 Jan 2021), §10.1, Proposition 10.5, conditions (a)–(c) and claim (ii), first inequality $\epsilon_B^s\ge\kappa/2$ (pp. 37–38).

import Definitions.Def_ExtendedSmale9_GeneralAlgorithm
import Definitions.Def_ExtendedSmale9_Delta1
import Definitions.Def_ExtendedSmale9_LinearProgram
import Mathlib

open scoped ENNReal

namespace ExtendedSmale9

theorem proposition_10_5_ii_strong {Ω Idx M : Type*} [Countable Idx] [MetricSpace M]
    (Λ : Idx → Ω → ℂ) (Ξ : Ω → Set M) (ι₁ ι₂ : ℕ+ → Ω)
    (S₁ S₂ : Set M) (κ : ℝ) (hκ : 0 < κ)
    (hsep : ∀ x₁ ∈ S₁, ∀ x₂ ∈ S₂, κ ≤ dist x₁ x₂)
    (hΞ₁ : ∀ n, Ξ (ι₁ n) ⊆ S₁) (hΞ₂ : ∀ n, Ξ (ι₂ n) ⊆ S₂)
    (ι₀ : Ω)
    (hc₁ : ∀ k n, ‖Λ k (ι₁ n) - Λ k ι₀‖ ≤ 1 / 4 ^ (n : ℕ))
    (hc₂ : ∀ k n, ‖Λ k (ι₂ n) - Λ k ι₀‖ ≤ 1 / 4 ^ (n : ℕ)) :
    ∃ fhat : Idx → ℕ+ → Ω → ℂ, IsDelta1Info Λ fhat ∧
      ENNReal.ofReal (κ / 2) ≤ strongBreakdownEps (delta1Eval fhat) Ξ := by sorry

end ExtendedSmale9
