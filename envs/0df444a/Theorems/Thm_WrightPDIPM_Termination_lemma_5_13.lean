-- Prove2me | Theorems.Thm_WrightPDIPM_Termination_lemma_5_13
-- name    : WrightPDIPM.Termination.lemma_5_13
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:54:11.55942+00:00
-- url     : https://prove2.me/theorems/bbec91d6-0850-4778-8569-d04a4b09168f
-- title:
--   Lemma 5.13 — in N₋∞(γ) with μ ≤ μ₀: ‖(x, s)‖ ≤ C₀, x_N, s_B ≤ μ/C₃ and x_B, s_N ≥ C₃γ, with C₃ = ε(A, b, c)/n
-- statement:
--   Let $A \in \mathbb{R}^{m\times n}$, $b \in \mathbb{R}^m$, $c \in \mathbb{R}^n$, let $\mu_0 > 0$ and $\gamma \in (0,1)$. Let $\mathcal B, \mathcal N$ be the optimal partition of $\{1,\dots,n\}$ (indices that are positive in some primal, respectively dual-slack, solution), let $\epsilon(A,b,c) = \min\bigl(\min_{i\in\mathcal B}\sup_{x^*\in\Omega_P} x^*_i, \min_{i\in\mathcal N}\sup_{(\lambda^*,s^*)\in\Omega_D} s^*_i\bigr)$ and $C_3 = \epsilon(A,b,c)/n$. Then there is a constant $C_0$ such that every $(x,\lambda,s) \in \mathcal N_{-\infty}(\gamma)$ with $\mu = x^{\mathsf T}s/n \le \mu_0$ satisfies
--   $$\|(x,s)\| \le C_0,$$
--   $$0 < x_i \le \mu/C_3\ (i \in \mathcal N),\qquad 0 < s_i \le \mu/C_3\ (i \in \mathcal B),$$
--   $$s_i \ge C_3\gamma\ (i \in \mathcal N),\qquad x_i \ge C_3\gamma\ (i \in \mathcal B).$$
--
--   The lemma says that iterates in the wide neighborhood reveal the optimal partition as $\mu \to 0$: the components that vanish at the solution are $O(\mu)$ and the others stay bounded away from zero. It is the basis of every finite-termination and superlinear-convergence argument of Chapter 7.
--
--   **Formalization Note** The book writes "there are constants $C_0$ and $C_3$"; its proof gives $C_3 = \epsilon(A,b,c)/n$ (5.32), which is used explicitly. $C_0$ (from Lemma 2.5 with $K = n\mu_0$) has no closed form and is existential, chosen before the point and depending only on $A, b, c, \mu_0, \gamma$. Norms are Euclidean. This restates Lemma 5.13 of Chapter 5 in this mission's namespace.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 101, Lemma 5.13 (C₃ from Eq. (5.32), p. 102)

import Mathlib
import Definitions.Def_WrightPDIPM_Termination_Setup

namespace WrightPDIPM.Termination

open Matrix

/-- Lemma 5.13 (p. 101): for `μ₀ > 0` and `γ ∈ (0, 1)` there is a constant `C₀` (chosen before
the point) such that every `(x, λ, s) ∈ N_{-∞}(γ)` with `μ ≤ μ₀` satisfies `‖(x, s)‖ ≤ C₀` (5.28),
and with the constant `C₃ = ε(A, b, c)/n` of (5.32) it satisfies (5.29)
`0 < xᵢ ≤ μ/C₃ (i ∈ N)`, `0 < sᵢ ≤ μ/C₃ (i ∈ B)` and (5.30) `sᵢ ≥ C₃γ (i ∈ N)`,
`xᵢ ≥ C₃γ (i ∈ B)`. -/
theorem lemma_5_13 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (μ₀ γ : ℝ) (hμ₀ : 0 < μ₀) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C₀ : ℝ, ∀ (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ),
      (x, lam, s) ∈ NegInf A b c γ → mu x s ≤ μ₀ →
        norm2Pair x s ≤ C₀ ∧
        (∀ i ∈ indexN A b c, 0 < x i ∧ x i ≤ mu x s / C3 A b c) ∧
        (∀ i ∈ indexB A b c, 0 < s i ∧ s i ≤ mu x s / C3 A b c) ∧
        (∀ i ∈ indexN A b c, C3 A b c * γ ≤ s i) ∧
        (∀ i ∈ indexB A b c, C3 A b c * γ ≤ x i) := by sorry

end WrightPDIPM.Termination
