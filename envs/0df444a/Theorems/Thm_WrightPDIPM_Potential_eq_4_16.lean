-- Prove2me | Theorems.Thm_WrightPDIPM_Potential_eq_4_16
-- name    : WrightPDIPM.Potential.eq_4_16
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:53:06.797986+00:00
-- url     : https://prove2.me/theorems/30ee4771-c6d7-4f3c-b4a8-ec2cb442522c
-- title:
--   Eq. (4.16) — along a feasible direction, Φ_ρ(x + αΔx, s + αΔs) ≤ q(α) for α ∈ (0, α_τ]
-- statement:
--   Let $(x,\lambda,s) \in \mathcal F^\circ$, $\rho > n$, and let $(\Delta x,\Delta\lambda,\Delta s)$ be a feasible direction: $A\Delta x = 0$ and $A^T\Delta\lambda + \Delta s = 0$ (4.12). Fix $\tau \in (0,1)$ and let $\alpha_\tau$ be defined by $\alpha_\tau\max(\|X^{-1}\Delta x\|_\infty, \|S^{-1}\Delta s\|_\infty) = \tau$ (4.14). Then for every $\alpha \in (0,\alpha_\tau]$,
--   $$\Phi_\rho(x+\alpha\Delta x, s+\alpha\Delta s) \le \Phi_\rho(x,s) + \alpha g_1 + \tfrac12\alpha^2 g_2 = q(\alpha), \qquad (4.16)$$
--   with $g_1 = \rho\frac{s^T\Delta x + x^T\Delta s}{x^Ts} - e^T(X^{-1}\Delta x + S^{-1}\Delta s)$ and $g_2 = \frac{1}{1-\tau}(\|X^{-1}\Delta x\|^2 + \|S^{-1}\Delta s\|^2)$ (4.17).
--
--   The convex quadratic $q$ is the model of the potential along the search direction from which the per-iteration decrease of Algorithm PR is read off.
--
--   **Formalization Note** The condition $\alpha \in (0,\alpha_\tau]$ is written $\alpha > 0$ and $\alpha\cdot\max(\|X^{-1}\Delta x\|_\infty, \|S^{-1}\Delta s\|_\infty) \le \tau$; this is the same condition when the maximum is positive, and when $\Delta x = \Delta s = 0$ (where (4.14) defines no $\alpha_\tau$) it allows every $\alpha > 0$, at which both sides equal $\Phi_\rho(x,s)$. $\rho > n$ is the range of (4.2); $q$ is `q ρ τ x s dx ds α` from the definition file.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, pp. 71–72, Eqs. (4.12)–(4.18), display (4.16)

import Mathlib
import Definitions.Def_WrightPDIPM_Potential_Setting

open Matrix

namespace WrightPDIPM.Potential

/-- **Eq. (4.16)** (Wright, pp. 71–72): the quadratic estimate of `Φ_ρ` along a feasible
direction. Let `(x, λ, s) ∈ F°`, `ρ > n`, and let `(Δx, Δλ, Δs)` satisfy (4.12),
`AΔx = 0`, `AᵀΔλ + Δs = 0`. Let `τ ∈ (0, 1)`. For every `α ∈ (0, α_τ]`, where
`α_τ max(‖X⁻¹Δx‖_∞, ‖S⁻¹Δs‖_∞) = τ` (4.14),
`Φ_ρ(x + αΔx, s + αΔs) ≤ Φ_ρ(x, s) + αg₁ + ½α²g₂ = q(α)` with `g₁, g₂` from (4.17).
The condition `α ∈ (0, α_τ]` is written `0 < α`, `α · max(‖X⁻¹Δx‖_∞, ‖S⁻¹Δs‖_∞) ≤ τ`. -/
theorem eq_4_16 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ) (hF : (x, lam, s) ∈ Fo A b c)
    (ρ : ℝ) (hρ : (n : ℝ) < ρ)
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ)
    (hdir : IsFeasibleDirection A dx dlam ds)
    (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (α : ℝ) (hα0 : 0 < α)
    (hατ : α * max (normInf (fun i => dx i / x i)) (normInf (fun i => ds i / s i)) ≤ τ) :
    Phi ρ (x + α • dx) (s + α • ds) ≤ q ρ τ x s dx ds α := by sorry

end WrightPDIPM.Potential
