-- Prove2me | Theorems.Thm_WrightPDIPM_Infeasible_lemma_6_7
-- name    : WrightPDIPM.Infeasible.lemma_6_7
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:54:11.144977+00:00
-- url     : https://prove2.me/theorems/fe4797af-5fcf-4c68-9b01-688d496e5f29
-- title:
--   Lemma 6.7 — a uniform ᾱ ∈ (0, 1) for which (6.37a)–(6.37c), (6.5) and (6.6) hold at every iterate
-- statement:
--   Let $(x^k,\lambda^k,s^k)$ be the iterates of Algorithm IPF for data $A \in \mathbb{R}^{m\times n}$, $b$, $c$, with parameters $\gamma \in (0,1)$, $\beta \ge 1$, $0 < \sigma_{\min} < \sigma_{\max} \le 0.5$ and search directions $(\Delta x^k,\Delta\lambda^k,\Delta s^k)$. Assume $n \ge 1$, $\Omega \ne \emptyset$, $(r_b^0,r_c^0) \ne 0$, and that the starting point lies in $\mathcal N_{-\infty}(\gamma,\beta)$. Then there is $\bar\alpha \in (0,1)$ such that for all $\alpha \in [0,\bar\alpha]$ and all $k \ge 0$:
--
--   $$\begin{aligned}
--   (x^k + \alpha\Delta x^k)^{\mathsf T}(s^k + \alpha\Delta s^k) &\ge (1-\alpha)(x^k)^{\mathsf T}s^k, && \text{(6.37a)}\\
--   (x^k_i + \alpha\Delta x^k_i)(s^k_i + \alpha\Delta s^k_i) &\ge (\gamma/n)(x^k + \alpha\Delta x^k)^{\mathsf T}(s^k + \alpha\Delta s^k) \quad (i = 1,\dots,n), && \text{(6.37b)}\\
--   (x^k + \alpha\Delta x^k)^{\mathsf T}(s^k + \alpha\Delta s^k) &\le (1 - .01\alpha)(x^k)^{\mathsf T}s^k, && \text{(6.37c)}
--   \end{aligned}$$
--
--   and therefore the step-length conditions of the algorithm hold: $(x^k,\lambda^k,s^k) + \alpha(\Delta x^k,\Delta\lambda^k,\Delta s^k) \in \mathcal N_{-\infty}(\gamma,\beta)$ (6.5) and $\mu_k(\alpha) \le (1 - .01\alpha)\mu_k$ (6.6).
--
--   Consequently every step length satisfies $\alpha_k \ge \bar\alpha$, which is what drives the linear decrease of $\mu_k$.
--
--   **Formalization Note** The starting point in $\mathcal N_{-\infty}(\gamma,\beta)$ is the setting of the convergence proof (p. 120: "from any starting point $(x^0,\lambda^0,s^0) \in \mathcal N_{-\infty}(\gamma,\beta)$"; p. 109, (6.3)); it is needed at $k = 0$, where (6.37b) at $\alpha = 0$ is the centrality of the start. $\Omega \ne \emptyset$ (pp. 127, 185; finding F1), $(r_b^0,r_c^0) \ne 0$ (p. 111) and $n \ge 1$ are explicit. The value of $\bar\alpha$ displayed at the end of the book's proof loses a factor $1/2$ against (6.47) and can equal 1 (finding F2); the statement is the existential one printed in the lemma. The second part of the lemma, (6.38), is the separate item `lemma_6_7_special`.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 118, Lemma 6.7, first part (proof pp. 119–120); start in N_−∞(γ, β) from pp. 109, 120; Ω ≠ ∅ from pp. 127, 185; (r_b⁰, r_c⁰) ≠ 0 from p. 111

import Mathlib
import Definitions.Def_WrightPDIPM_Infeasible_IPF

namespace WrightPDIPM.Infeasible

open Filter

/-- Lemma 6.7, first part (p. 118): along Algorithm IPF started in `N_{-∞}(γ, β)`, with `Ω ≠ ∅`
and an infeasible start, there is `ᾱ ∈ (0, 1)` such that for all `α ∈ [0, ᾱ]` and all `k ≥ 0`
the three inequalities (6.37a)–(6.37c) hold, and therefore the step-length conditions (6.5)
(membership in `N_{-∞}(γ, β)`) and (6.6) (the Armijo condition) hold. -/
theorem lemma_6_7 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (γ β σmin σmax : ℝ) (hγ : 0 < γ ∧ γ < 1) (hβ : 1 ≤ β)
    (hσ : 0 < σmin ∧ σmin < σmax ∧ σmax ≤ 0.5)
    (hn : 0 < n)
    (x : ℕ → Fin n → ℝ) (lam : ℕ → Fin m → ℝ) (s : ℕ → Fin n → ℝ) (σ α : ℕ → ℝ)
    (dx : ℕ → Fin n → ℝ) (dlam : ℕ → Fin m → ℝ) (ds : ℕ → Fin n → ℝ)
    (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds)
    (hinf : (rb A b (x 0), rc A c (lam 0) (s 0)) ≠ (0, 0))
    (hΩ : (Omega A b c).Nonempty)
    (hstart : (x 0, lam 0, s 0) ∈ NegInfNbhd A b c γ β (x 0) (lam 0) (s 0)) :
    ∃ αbar : ℝ, 0 < αbar ∧ αbar < 1 ∧ ∀ a ∈ Set.Icc (0 : ℝ) αbar, ∀ k,
        (x k + a • dx k) ⬝ᵥ (s k + a • ds k) ≥ (1 - a) * (x k ⬝ᵥ s k) ∧
        (∀ i, (x k i + a * dx k i) * (s k i + a * ds k i) ≥
          (γ / n) * ((x k + a • dx k) ⬝ᵥ (s k + a • ds k))) ∧
        (x k + a • dx k) ⬝ᵥ (s k + a • ds k) ≤ (1 - 0.01 * a) * (x k ⬝ᵥ s k) ∧
        (x k + a • dx k, lam k + a • dlam k, s k + a • ds k) ∈
          NegInfNbhd A b c γ β (x 0) (lam 0) (s 0) ∧
        mu (x k + a • dx k) (s k + a • ds k) ≤ (1 - 0.01 * a) * mu (x k) (s k) := by sorry

end WrightPDIPM.Infeasible
