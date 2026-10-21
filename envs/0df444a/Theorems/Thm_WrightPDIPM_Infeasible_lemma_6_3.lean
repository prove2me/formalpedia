-- Prove2me | Theorems.Thm_WrightPDIPM_Infeasible_lemma_6_3
-- name    : WrightPDIPM.Infeasible.lemma_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:53:58.336769+00:00
-- url     : https://prove2.me/theorems/7e61fcfe-9a3c-4c64-9740-263e990bb567
-- title:
--   Lemma 6.3 — ν_k‖(x^k, s^k)‖₁ ≤ C₁μ_k along Algorithm IPF
-- statement:
--   Let $(x^k,\lambda^k,s^k)$ be the iterates of Algorithm IPF for the linear program with data $A \in \mathbb{R}^{m\times n}$, $b$, $c$, run with parameters $\gamma \in (0,1)$, $\beta \ge 1$, $0 < \sigma_{\min} < \sigma_{\max} \le 0.5$ from a starting point with $(x^0,s^0) > 0$. Let $\mu_k = (x^k)^{\mathsf T}s^k/n$ and $\nu_k = \prod_{j=0}^{k-1}(1-\alpha_j)$, where $\alpha_j$ are the step lengths. Assume $n \ge 1$, that the primal-dual solution set $\Omega$ is nonempty, and that the starting point is infeasible, $(r_b^0, r_c^0) \ne 0$. Then there is a positive constant $C_1$ such that
--
--   $$\nu_k\,\|(x^k,s^k)\|_1 \le C_1\mu_k \qquad \text{for all } k \ge 0.$$
--
--   The bound says that the weight $\nu_k$ of the infeasible starting point in the current iterate cannot keep large components of $(x^k, s^k)$ alive as $\mu_k$ decreases; it is the first of the estimates on which the uniform lower bound on the step length rests.
--
--   **Formalization Note** $C_1$ is quantified before $k$: it may depend on the data, the parameters, the run and a solution, never on $k$. The hypotheses $\Omega \neq \emptyset$ (the proof starts from "any primal-dual solution"; the book states the assumption on pp. 127 and 185, see finding F1) and $(r_b^0,r_c^0) \ne 0$ (the chapter's standing assumption, p. 111) are explicit, as is $n \ge 1$, which $\mu = x^{\mathsf T}s/n$ presupposes. The proof gives $C_1 = \xi^{-1}[\beta n + n + \beta\|(x^0,s^0)\|_\infty\|(x^*,s^*)\|_1/\mu_0]$ with $\xi = \min_i \min(x^0_i, s^0_i)$.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 113, Lemma 6.3 (proof pp. 113–114); Ω ≠ ∅ from pp. 127, 185; (r_b⁰, r_c⁰) ≠ 0 from p. 111

import Mathlib
import Definitions.Def_WrightPDIPM_Infeasible_IPF

namespace WrightPDIPM.Infeasible

open Filter

/-- Lemma 6.3 (p. 113): along Algorithm IPF, with `Ω ≠ ∅` and an infeasible start, there is a
positive constant `C₁` (independent of `k`) with `ν_k ‖(xᵏ, sᵏ)‖₁ ≤ C₁ μ_k` for all `k ≥ 0`. -/
theorem lemma_6_3 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (γ β σmin σmax : ℝ) (hγ : 0 < γ ∧ γ < 1) (hβ : 1 ≤ β)
    (hσ : 0 < σmin ∧ σmin < σmax ∧ σmax ≤ 0.5)
    (hn : 0 < n)
    (x : ℕ → Fin n → ℝ) (lam : ℕ → Fin m → ℝ) (s : ℕ → Fin n → ℝ) (σ α : ℕ → ℝ)
    (dx : ℕ → Fin n → ℝ) (dlam : ℕ → Fin m → ℝ) (ds : ℕ → Fin n → ℝ)
    (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds)
    (hinf : (rb A b (x 0), rc A c (lam 0) (s 0)) ≠ (0, 0))
    (hΩ : (Omega A b c).Nonempty) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ k, nu α k * norm1xs (x k) (s k) ≤ C₁ * mu (x k) (s k) := by sorry

end WrightPDIPM.Infeasible
