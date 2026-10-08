-- Prove2me | Theorems.Thm_WorstCaseCVaR_Box_feasible_24_to_16
-- name    : WorstCaseCVaR.Box.feasible_24_to_16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T18:03:23.7497+00:00
-- url     : https://prove2.me/theorems/348e315b-e132-47a4-be9f-8d0eb781b47d
-- title:
--   Proof of Proposition 2 — a feasible point of (24)–(30) projects to a feasible point of (16)–(20)
-- statement:
--   Let $f : \mathbb R^n \times \mathbb R^m \to \mathbb R$, scenarios $y_{[1]}, \dots, y_{[S]} \in \mathbb R^m$, a set $\mathcal X \subseteq \mathbb R^n$, $0 < \beta < 1$, and box data $\pi^0, \underline\eta, \overline\eta \in \mathbb R^S$ be given. If $(x, u, z, \xi, \omega, \alpha, \theta)$ is feasible to (24)–(30), then $(x, u, \alpha, \theta)$ is feasible to (16)–(20) with $\mathcal P_\pi = \mathcal P_\pi^B$; in particular
--   $$\alpha + \frac{1}{1-\beta}\pi^\top u \le \theta \qquad \text{for all } \pi \in \mathcal P_\pi^B.$$
--
--   Together with the reverse transfer, this shows the two problems have the same optimal value, which is the content of Proposition 2.
--
--   **Formalization Note** Constraint (18) is in its "for all $\pi$" form (see the definition of the problems). No convexity of $f$ and no structure on $\mathcal X$ is assumed.
-- source:
--   Zhu & Fukushima, Worst-Case Conditional Value-at-Risk with Application to Robust Portfolio Management, Oper. Res. 57(5), 2009, p. 1167, proof of Proposition 2

import Mathlib
import Definitions.Def_WorstCaseCVaR_Box_Problems

open Matrix

namespace WorstCaseCVaR.Box

/-- Proof of Proposition 2, p. 1167: if `(x, u, z, ξ, ω, α, θ)` is feasible to (24)–(30),
then `(x, u, α, θ)` is feasible to (16)–(20) with `𝒫_π = 𝒫_π^B`. -/
theorem feasible_24_to_16 {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (ys : Fin S → Fin m → ℝ) (𝒳 : Set (Fin n → ℝ)) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (π0 ηlo ηhi : Fin S → ℝ) :
    ∀ q ∈ feas24 f ys 𝒳 β π0 ηlo ηhi, q.toVar16 ∈ feas16 f ys 𝒳 β π0 ηlo ηhi := by sorry

end WorstCaseCVaR.Box
