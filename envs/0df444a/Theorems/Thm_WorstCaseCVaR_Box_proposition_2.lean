-- Prove2me | Theorems.Thm_WorstCaseCVaR_Box_proposition_2
-- name    : WorstCaseCVaR.Box.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T18:05:21.29988+00:00
-- url     : https://prove2.me/theorems/5a0378f7-9d6d-44a1-99f8-b7f22fa05fb2
-- title:
--   Proposition 2 — under box uncertainty, worst-case CVaR minimization (16)–(20) is equivalent to the LP (24)–(30)
-- statement:
--   Let $f : \mathbb R^n \times \mathbb R^m \to \mathbb R$ be a loss function, $y_{[1]}, \dots, y_{[S]} \in \mathbb R^m$ the scenarios of the random vector, $\mathcal X \subseteq \mathbb R^n$ the decision set, $0 < \beta < 1$ the confidence level, and let the distribution $\pi$ range over the box
--   $$\mathcal P_\pi^B = \{\pi : \pi = \pi^0 + \eta,\ e^\top\eta = 0,\ \underline\eta \le \eta \le \overline\eta\}.$$
--   Then:
--
--   1. If $(x^*, u^*, z^*, \xi^*, \omega^*, \alpha^*, \theta^*)$ solves (24)–(30), then $(x^*, u^*, \alpha^*, \theta^*)$ solves (16)–(20) with $\mathcal P_\pi = \mathcal P_\pi^B$.
--   2. Conversely, if $(\tilde x^*, \tilde u^*, \tilde\alpha^*, \tilde\theta^*)$ solves (16)–(20) with $\mathcal P_\pi = \mathcal P_\pi^B$, then $(\tilde x^*, \tilde u^*, \tilde z^*, \tilde\xi^*, \tilde\omega^*, \tilde\alpha^*, \tilde\theta^*)$ solves (24)–(30) for every optimal solution $(\tilde z^*, \tilde\xi^*, \tilde\omega^*)$ of the linear program (23) with $u = \tilde u^*$,
--   $$\min_{(z,\xi,\omega)}\{\overline\eta^\top\xi + \underline\eta^\top\omega : e z + \xi + \omega = \tilde u^*,\ \xi \ge 0,\ \omega \le 0\},$$
--   3. and such an optimal solution of (23) exists.
--
--   Here "solves" means: feasible, with objective value $\theta$ minimal among all feasible points. The proposition turns the semi-infinite worst-case CVaR problem (16)–(20) into a single finite problem (24)–(30), a linear program when $f$ is linear in $x$ and $\mathcal X$ is a polyhedron.
--
--   **Formalization Note** Constraint (18) is in its equivalent "for all $\pi \in \mathcal P_\pi^B$" form. Clause 3 makes explicit the existence that the paper's "where $(\tilde z^*, \tilde\xi^*, \tilde\omega^*)$ is an optimal solution to (23)" presupposes. No hypothesis on $f$, $\mathcal X$, $\pi^0$, $\underline\eta$, $\overline\eta$ is added: when $\mathcal P_\pi^B$ is empty neither problem has an optimal solution, so the statement holds for all data.
-- source:
--   Zhu & Fukushima, Worst-Case Conditional Value-at-Risk with Application to Robust Portfolio Management, Oper. Res. 57(5), 2009, p. 1159, Proposition 2 (proof pp. 1167–1168)

import Mathlib
import Definitions.Def_WorstCaseCVaR_Box_Problems

open Matrix

namespace WorstCaseCVaR.Box

/-- Proposition 2, p. 1159. (1) If `(x*, u*, z*, ξ*, ω*, α*, θ*)` solves (24)–(30), then
`(x*, u*, α*, θ*)` solves (16)–(20) with `𝒫_π = 𝒫_π^B`. (2) Conversely, if `(x̃*, ũ*, α̃*, θ̃*)`
solves (16)–(20) with `𝒫_π = 𝒫_π^B`, then `(x̃*, ũ*, z̃*, ξ̃*, ω̃*, α̃*, θ̃*)` solves (24)–(30)
for every optimal solution `(z̃*, ξ̃*, ω̃*)` of (23) with `u = ũ*`; (3) such an optimal
solution exists. -/
theorem proposition_2 {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (ys : Fin S → Fin m → ℝ) (𝒳 : Set (Fin n → ℝ)) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (π0 ηlo ηhi : Fin S → ℝ) :
    (∀ q : Var24 n S, Solves24 f ys 𝒳 β π0 ηlo ηhi q →
      Solves16 f ys 𝒳 β π0 ηlo ηhi q.toVar16) ∧
    (∀ p : Var16 n S, Solves16 f ys 𝒳 β π0 ηlo ηhi p →
      ∀ d : Dual23 S, IsOptimal23 ηlo ηhi p.u d →
        Solves24 f ys 𝒳 β π0 ηlo ηhi (p.withDual d)) ∧
    (∀ p : Var16 n S, Solves16 f ys 𝒳 β π0 ηlo ηhi p →
      ∃ d : Dual23 S, IsOptimal23 ηlo ηhi p.u d) := by sorry

end WorstCaseCVaR.Box
