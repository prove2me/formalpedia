-- Prove2me | Theorems.Thm_WrightPDIPM_Termination_theorem_7_12
-- name    : WrightPDIPM.Termination.theorem_7_12
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:54:12.142597+00:00
-- url     : https://prove2.me/theorems/c8960539-4782-4513-acf9-a9d0f53cb769
-- title:
--   Theorem 7.12 — below a threshold μ̄ > 0 in N₋∞(γ), (7.40) finds B and N and the projection (7.41) returns a strictly complementary solution
-- statement:
--   Let $A \in \mathbb{R}^{m\times n}$, $b \in \mathbb{R}^m$, $c \in \mathbb{R}^n$ (no rank assumption) and $\gamma \in (0,1)$. Let $\mathcal B, \mathcal N$ be the optimal partition: $\mathcal B$ the indices $j$ with $x^*_j \ne 0$ for some primal solution $x^*$, $\mathcal N$ the indices with $s^*_j \ne 0$ for some dual solution $(\lambda^*, s^*)$. For a point $(x,\lambda,s)$ define the estimates $\mathcal B(x,s) = \{i : x_i \ge s_i\}$ and $\mathcal N(x,s) = \{1,\dots,n\} \setminus \mathcal B(x,s)$, and the projection problem
--   $$\min_{(x^*,\lambda^*,s^*)} \tfrac12\|x^*-x\|^2 + \tfrac12\|s^*-s\|^2 \ \text{ s.t. } Ax^* = b,\ A^{\mathsf T}\lambda^* + s^* = c,\ x^*_i = 0\ (i\in\mathcal N(x,s)),\ s^*_i = 0\ (i \in \mathcal B(x,s)).$$
--   Then there is a threshold $\bar\mu > 0$ such that for every $(x,\lambda,s) \in \mathcal N_{-\infty}(\gamma)$ with
--   $$0 < \mu = x^{\mathsf T}s/n \le \bar\mu$$
--   we have
--   (i) $\mathcal B(x,s) = \mathcal B$ and $\mathcal N(x,s) = \mathcal N$; and
--   (ii) the projection problem has a solution, and every solution $(x^*,\lambda^*,s^*)$ is a strictly complementary primal-dual solution: $(x^*,\lambda^*,s^*) \in \Omega$, $x^*_i > 0$ for $i \in \mathcal B$ and $s^*_i > 0$ for $i \in \mathcal N$.
--
--   This is Ye's finite termination result: once a path-following method has driven $\mu$ below $\bar\mu$, one least-squares projection jumps to an exact strictly complementary solution.
--
--   **Formalization Note** The book's statement is existential in $\bar\mu$ and is kept so; $\bar\mu > 0$ is stated explicitly (a threshold $0$ would make the theorem vacuous). The proof's value (7.48) is $\bar\mu = \frac{\epsilon(A,b,c)^2\gamma}{2n^2}\min(1, 1/(\hat C n^{1/2}))$, with $\hat C$ the Hoffman constant of the constraint system (7.44); it is not imposed. "The projection yields a strictly complementary solution" is read as: a minimizer exists, and every minimizer is strictly complementary ($\lambda^*$ is not unique, since it does not enter the objective). $\mathcal N_{-\infty}(\gamma) \subset \mathcal F^\circ$ by definition; $\Omega \ne \emptyset$ is not assumed separately (it follows from $\mathcal F^\circ \neq \emptyset$). Norms are Euclidean.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, pp. 147–148, Theorem 7.12

import Mathlib
import Definitions.Def_WrightPDIPM_Termination_Setup

namespace WrightPDIPM.Termination

open Matrix

/-- Theorem 7.12 (pp. 147–148): for `γ ∈ (0, 1)` there is a threshold `μ̄ > 0` such that for
every `(x, λ, s) ∈ N_{-∞}(γ)` with `0 < μ = xᵀs/n ≤ μ̄`:
(i) the estimate (7.40) is exact, `B(x, s) = B` and `N(x, s) = N`;
(ii) the projection problem (7.41) has a solution, and every solution `(x*, λ*, s*)` of it is a
strictly complementary solution (5.26). -/
theorem theorem_7_12 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ μbar : ℝ, 0 < μbar ∧ ∀ (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ),
      (x, lam, s) ∈ NegInf A b c γ → 0 < mu x s → mu x s ≤ μbar →
        (Bset x s = indexB A b c ∧ Nset x s = indexN A b c) ∧
        (∃ p, IsFTMinimizer A b c x s p) ∧
        ∀ p, IsFTMinimizer A b c x s p → IsStrictlyComplementary A b c p := by sorry

end WrightPDIPM.Termination
