-- Prove2me | Theorems.Thm_WorstCaseCVaR_Box_feasible_16_to_24
-- name    : WorstCaseCVaR.Box.feasible_16_to_24
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T18:04:00.250251+00:00
-- url     : https://prove2.me/theorems/e6dd6cb8-1072-4809-9862-95a18ede172a
-- title:
--   Proof of Proposition 2 — a feasible point of (16)–(20) plus an optimal solution of (23) is feasible to (24)–(30)
-- statement:
--   Let $f : \mathbb R^n \times \mathbb R^m \to \mathbb R$, scenarios $y_{[1]}, \dots, y_{[S]} \in \mathbb R^m$, a set $\mathcal X \subseteq \mathbb R^n$, $0 < \beta < 1$, and box data $\pi^0, \underline\eta, \overline\eta \in \mathbb R^S$ be given. If $(x, u, \alpha, \theta)$ is feasible to (16)–(20) with $\mathcal P_\pi = \mathcal P_\pi^B$ and $(z, \xi, \omega)$ is an optimal solution of the linear program (23) with this $u$, then $(x, u, z, \xi, \omega, \alpha, \theta)$ is feasible to (24)–(30); in particular
--   $$\alpha + \frac{1}{1-\beta}(\pi^0)^\top u + \frac{1}{1-\beta}(\overline\eta^\top\xi + \underline\eta^\top\omega) \le \theta.$$
--
--   This is the feasibility half of the converse direction of Proposition 2.
-- source:
--   Zhu & Fukushima, Worst-Case Conditional Value-at-Risk with Application to Robust Portfolio Management, Oper. Res. 57(5), 2009, pp. 1167–1168, proof of Proposition 2

import Mathlib
import Definitions.Def_WorstCaseCVaR_Box_Problems

open Matrix

namespace WorstCaseCVaR.Box

/-- Proof of Proposition 2, pp. 1167–1168: if `(x, u, α, θ)` is feasible to (16)–(20) with
`𝒫_π = 𝒫_π^B` and `(z, ξ, ω)` is an optimal solution to (23) with this `u`, then
`(x, u, z, ξ, ω, α, θ)` is feasible to (24)–(30). -/
theorem feasible_16_to_24 {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (ys : Fin S → Fin m → ℝ) (𝒳 : Set (Fin n → ℝ)) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (π0 ηlo ηhi : Fin S → ℝ) :
    ∀ p ∈ feas16 f ys 𝒳 β π0 ηlo ηhi, ∀ d, IsOptimal23 ηlo ηhi p.u d →
      p.withDual d ∈ feas24 f ys 𝒳 β π0 ηlo ηhi := by sorry

end WorstCaseCVaR.Box
