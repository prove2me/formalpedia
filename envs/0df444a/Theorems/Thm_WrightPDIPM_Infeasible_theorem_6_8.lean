-- Prove2me | Theorems.Thm_WrightPDIPM_Infeasible_theorem_6_8
-- name    : WrightPDIPM.Infeasible.theorem_6_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:54:03.393226+00:00
-- url     : https://prove2.me/theorems/9b408f1d-caba-452c-bbf3-afb18c8ef0ae
-- title:
--   Theorem 6.8 — bounds (6.49)–(6.50) on the iterates and strict complementarity of limit points
-- statement:
--   Let $(x^k,\lambda^k,s^k)$ be the iterates of Algorithm IPF for data $A \in \mathbb{R}^{m\times n}$, $b$, $c$, with parameters $\gamma \in (0,1)$, $\beta \ge 1$, $0 < \sigma_{\min} < \sigma_{\max} \le 0.5$, and $\mu_k = (x^k)^{\mathsf T}s^k/n$. Assume $n \ge 1$, $\Omega \ne \emptyset$ and $(r_b^0,r_c^0) \ne 0$. Let $\mathcal B = \{j : x^*_j \ne 0$ for some solution$\}$ and $\mathcal N = \{j : s^*_j \ne 0$ for some solution$\}$. Then there is a constant $C_3 > 0$ such that for all $k$ sufficiently large
--
--   $$0 < x^k_i \le \mu_k/C_3 \ (i \in \mathcal N), \quad 0 < s^k_i \le \mu_k/C_3 \ (i \in \mathcal B), \quad s^k_i \ge C_3\gamma \ (i \in \mathcal N), \quad x^k_i \ge C_3\gamma \ (i \in \mathcal B).$$
--
--   Moreover, for every limit point $(x^*,s^*)$ of the sequence $\{(x^k,s^k)\}$ there is $\lambda^*$ such that $(x^*,\lambda^*,s^*)$ is a strictly complementary primal-dual solution: $(x^*,\lambda^*,s^*) \in \Omega$ and $x^* + s^* > 0$.
--
--   The iterates thus identify the optimal partition: the components that vanish at the solution decrease like $\mu_k$, the others stay bounded away from zero.
--
--   **Formalization Note** "Any limit point can be used to construct a strictly complementary solution" is rendered as: for every cluster point $(x^*,s^*)$ of $k \mapsto (x^k,s^k)$ there is $\lambda^*$ with $(x^*,\lambda^*,s^*) \in \Omega$ and $x^*_i + s^*_i > 0$ for all $i$. $C_3 > 0$ is stated, and it is quantified before the threshold on $k$. $\Omega \ne \emptyset$ (pp. 127, 185; finding F1), $(r_b^0,r_c^0) \ne 0$ (p. 111) and $n \ge 1$ are explicit.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 121, Theorem 6.8 (proof pp. 121–123); B, N from (2.11), p. 27; Ω ≠ ∅ from pp. 127, 185; (r_b⁰, r_c⁰) ≠ 0 from p. 111

import Mathlib
import Definitions.Def_WrightPDIPM_Infeasible_IPF

namespace WrightPDIPM.Infeasible

open Filter

/-- Theorem 6.8 (p. 121): along Algorithm IPF, with `Ω ≠ ∅` and an infeasible start, there is a
constant `C₃ > 0` such that for all `k` sufficiently large `0 < xᵢᵏ ≤ μ_k/C₃` (`i ∈ N`),
`0 < sᵢᵏ ≤ μ_k/C₃` (`i ∈ B`) (6.49), `sᵢᵏ ≥ C₃γ` (`i ∈ N`), `xᵢᵏ ≥ C₃γ` (`i ∈ B`) (6.50); and every
limit point `(x*, s*)` of `{(xᵏ, sᵏ)}` gives a strictly complementary solution `(x*, λ*, s*)`
for some `λ*`. -/
theorem theorem_6_8 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (γ β σmin σmax : ℝ) (hγ : 0 < γ ∧ γ < 1) (hβ : 1 ≤ β)
    (hσ : 0 < σmin ∧ σmin < σmax ∧ σmax ≤ 0.5)
    (hn : 0 < n)
    (x : ℕ → Fin n → ℝ) (lam : ℕ → Fin m → ℝ) (s : ℕ → Fin n → ℝ) (σ α : ℕ → ℝ)
    (dx : ℕ → Fin n → ℝ) (dlam : ℕ → Fin m → ℝ) (ds : ℕ → Fin n → ℝ)
    (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds)
    (hinf : (rb A b (x 0), rc A c (lam 0) (s 0)) ≠ (0, 0))
    (hΩ : (Omega A b c).Nonempty) :
    (∃ C₃ : ℝ, 0 < C₃ ∧ ∀ᶠ k in atTop,
      (∀ i ∈ indexN A b c, 0 < x k i ∧ x k i ≤ mu (x k) (s k) / C₃) ∧
      (∀ i ∈ indexB A b c, 0 < s k i ∧ s k i ≤ mu (x k) (s k) / C₃) ∧
      (∀ i ∈ indexN A b c, C₃ * γ ≤ s k i) ∧
      (∀ i ∈ indexB A b c, C₃ * γ ≤ x k i)) ∧
    ∀ q : (Fin n → ℝ) × (Fin n → ℝ), MapClusterPt q atTop (fun k => (x k, s k)) →
      ∃ lamstar : Fin m → ℝ, (q.1, lamstar, q.2) ∈ Omega A b c ∧ ∀ i, 0 < q.1 i + q.2 i := by sorry

end WrightPDIPM.Infeasible
