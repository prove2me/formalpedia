-- Prove2me | Theorems.Thm_WrightPDIPM_Infeasible_lemma_6_4
-- name    : WrightPDIPM.Infeasible.lemma_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:54:00.481422+00:00
-- url     : https://prove2.me/theorems/54f2019d-2edf-4072-b2ce-76e2e32f829e
-- title:
--   Lemma 6.4 — ζν_k‖(x^k, s^k)‖₁ ≤ 4βnμ_k for the start (ζe, 0, ζe)
-- statement:
--   Let $(x^k,\lambda^k,s^k)$ be the iterates of Algorithm IPF for data $A \in \mathbb{R}^{m\times n}$, $b$, $c$, with parameters $\gamma \in (0,1)$, $\beta \ge 1$, $0 < \sigma_{\min} < \sigma_{\max} \le 0.5$, and let $\mu_k = (x^k)^{\mathsf T}s^k/n$, $\nu_k = \prod_{j=0}^{k-1}(1-\alpha_j)$. Assume $n \ge 1$ and that the starting point is the special point
--
--   $$(x^0,\lambda^0,s^0) = (\zeta e, 0, \zeta e), \qquad \|(x^*,s^*)\|_\infty \le \zeta \ \text{ for some primal-dual solution } (x^*,\lambda^*,s^*),$$
--
--   and that it is infeasible, $(r_b^0,r_c^0) \ne 0$. Then every iterate satisfies
--
--   $$\zeta\,\nu_k\,\|(x^k,s^k)\|_1 \le 4\beta n\,\mu_k .$$
--
--   This is the special case of Lemma 6.3 in which the constant is explicit in $n$; it is the first step towards the polynomial complexity of the method.
--
--   **Formalization Note** The existence of the solution $(x^*,\lambda^*,s^*)$ in (6.13) makes $\Omega$ nonempty, so no separate hypothesis is needed; $\zeta > 0$ follows from $(x^0,s^0) > 0$. The standing assumption $(r_b^0,r_c^0) \ne 0$ (p. 111) and $n \ge 1$ are explicit. $\|(x^*,s^*)\|_\infty \le \zeta$ is written componentwise as $|x^*_i| \le \zeta$, $|s^*_i| \le \zeta$.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 114, Lemma 6.4 (proof pp. 114–115); starting point (6.12)–(6.13), p. 112; (r_b⁰, r_c⁰) ≠ 0 from p. 111

import Mathlib
import Definitions.Def_WrightPDIPM_Infeasible_IPF

namespace WrightPDIPM.Infeasible

open Filter

/-- Lemma 6.4 (p. 114): with the starting point (6.12)–(6.13), `(x⁰, λ⁰, s⁰) = (ζe, 0, ζe)` and
`‖(x*, s*)‖_∞ ≤ ζ` for some primal-dual solution, every iterate satisfies
`ζ ν_k ‖(xᵏ, sᵏ)‖₁ ≤ 4βnμ_k`. -/
theorem lemma_6_4 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (γ β σmin σmax : ℝ) (hγ : 0 < γ ∧ γ < 1) (hβ : 1 ≤ β)
    (hσ : 0 < σmin ∧ σmin < σmax ∧ σmax ≤ 0.5)
    (hn : 0 < n)
    (x : ℕ → Fin n → ℝ) (lam : ℕ → Fin m → ℝ) (s : ℕ → Fin n → ℝ) (σ α : ℕ → ℝ)
    (dx : ℕ → Fin n → ℝ) (dlam : ℕ → Fin m → ℝ) (ds : ℕ → Fin n → ℝ)
    (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds)
    (hinf : (rb A b (x 0), rc A c (lam 0) (s 0)) ≠ (0, 0))
    (ζ : ℝ) (hx0 : x 0 = fun _ => ζ) (hlam0 : lam 0 = 0) (hs0 : s 0 = fun _ => ζ)
    (hζ : ∃ p ∈ Omega A b c, ∀ i, |p.1 i| ≤ ζ ∧ |p.2.2 i| ≤ ζ) :
    ∀ k, ζ * nu α k * norm1xs (x k) (s k) ≤ 4 * β * n * mu (x k) (s k) := by sorry

end WrightPDIPM.Infeasible
