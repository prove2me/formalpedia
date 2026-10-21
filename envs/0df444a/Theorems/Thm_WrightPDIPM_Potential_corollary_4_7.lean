-- Prove2me | Theorems.Thm_WrightPDIPM_Potential_corollary_4_7
-- name    : WrightPDIPM.Potential.corollary_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:53:13.588436+00:00
-- url     : https://prove2.me/theorems/a2b97f0c-3e45-4495-8ea2-4024508721be
-- title:
--   Corollary 4.7 — Algorithm PR reaches μ_k ≤ ε for all k ≥ ⌈((κ + 1)/0.15)(ρ − n)|log ε|⌉
-- statement:
--   Let $n \ge 1$, fix $\rho \ge n + \sqrt n$ and $\epsilon > 0$, and let $(x^k,\lambda^k,s^k)_{k\ge0}$ be the iterates of Algorithm PR started at $(x^0,\lambda^0,s^0) \in \mathcal F^\circ$: at each $k$, $(\Delta x^k,\Delta\lambda^k,\Delta s^k)$ solves $A\Delta x = 0$, $A^T\Delta\lambda + \Delta s = 0$, $S^k\Delta x + X^k\Delta s = -X^kS^ke + \frac n\rho\mu_ke$, the step length $\alpha_k \in (0,\alpha_{\max})$ minimizes $\Phi_\rho(x^k+\alpha\Delta x^k, s^k+\alpha\Delta s^k)$ over $(0,\alpha_{\max})$, and $(x^{k+1},\lambda^{k+1},s^{k+1}) = (x^k,\lambda^k,s^k) + \alpha_k(\Delta x^k,\Delta\lambda^k,\Delta s^k)$. Suppose
--   $$\Phi_\rho(x^0,s^0) \le \kappa(\rho-n)|\log\epsilon|$$
--   for some $\kappa > 0$. Then the index
--   $$K = \left\lceil \frac{\kappa+1}{0.15}(\rho-n)|\log\epsilon| \right\rceil \qquad (4.32)$$
--   has the property that $(x^k,\lambda^k,s^k) \in \mathcal F^\circ$ and $\mu_k \le \epsilon$ for all $k \ge K$.
--
--   At $\rho = n + \sqrt n$ this is the $O(\sqrt n|\log\epsilon|)$ iteration bound of the primal-dual potential-reduction method.
--
--   **Formalization Note** The book writes $K = O((\rho-n)|\log\epsilon|)$ after the explicit formula; the formula is what is stated. "$\kappa$ independent of $n$" concerns that $O(\cdot)$ and is not a hypothesis of the bound. The iterates are given as a sequence each of whose steps is a PR iteration (`IsPRStep`), with the minimizing step length as data; membership in $\mathcal F^\circ$ is assumed only at $k = 0$ and concluded for $k \ge K$. $\epsilon > 0$ as printed (not $\epsilon < 1$). $n \ge 1$ is implicit in the book.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, pp. 77–78, Corollary 4.7

import Mathlib
import Definitions.Def_WrightPDIPM_Potential_Setting

open Matrix

namespace WrightPDIPM.Potential

/-- **Corollary 4.7** (Wright, pp. 77–78). Fix `ρ ≥ n + √n` (`n ≥ 1`) and `ε > 0`, and let
`(xᵏ, λᵏ, sᵏ)` be the iterates of Algorithm PR (p. 67) from an initial point
`(x⁰, λ⁰, s⁰) ∈ F°` with `Φ_ρ(x⁰, s⁰) ≤ κ(ρ − n)|log ε|` for some `κ > 0`. Then the index
`K = ⌈((κ + 1)/0.15)(ρ − n)|log ε|⌉` (4.32) has the property that `(xᵏ, λᵏ, sᵏ) ∈ F°` and
`μ_k ≤ ε` for all `k ≥ K`. Each iteration is `IsPRStep`: the direction of (1.13) with
`σ_k = n/ρ` and a step length `α_k` minimizing `Φ_ρ` along it over `(0, α_max)` (4.6). -/
theorem corollary_4_7 {m n : ℕ} (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (ρ : ℝ) (hρ : (n : ℝ) + Real.sqrt n ≤ ρ) (ε : ℝ) (hε : 0 < ε)
    (κ : ℝ) (hκ : 0 < κ)
    (x : ℕ → Fin n → ℝ) (lam : ℕ → Fin m → ℝ) (s : ℕ → Fin n → ℝ)
    (h0 : (x 0, lam 0, s 0) ∈ Fo A b c)
    (hPR : ∀ k, IsPRStep A ρ (x k) (lam k) (s k) (x (k + 1)) (lam (k + 1)) (s (k + 1)))
    (hΦ0 : Phi ρ (x 0) (s 0) ≤ κ * (ρ - n) * |Real.log ε|) :
    ∀ k : ℕ, ⌈(κ + 1) / (15 / 100) * (ρ - n) * |Real.log ε|⌉ ≤ (k : ℤ) →
      (x k, lam k, s k) ∈ Fo A b c ∧ mu (x k) (s k) ≤ ε := by sorry

end WrightPDIPM.Potential
