-- Prove2me | Theorems.Thm_WrightPDIPM_Potential_theorem_4_4
-- name    : WrightPDIPM.Potential.theorem_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:53:12.048228+00:00
-- url     : https://prove2.me/theorems/f4c3691f-b342-44de-8437-9043a377cd0c
-- title:
--   Theorem 4.4 — a constant decrease δ of Φ_ρ gives μ_k ≤ ε for k ≥ ⌈Φ_ρ(x⁰, s⁰)/δ + ((ρ − n)/δ)|log ε|⌉
-- statement:
--   Let $\rho > n$ and let $(x^k,\lambda^k,s^k)_{k\ge0}$ be any sequence in the strictly feasible set $\mathcal F^\circ$ of the primal-dual pair, starting from $(x^0,\lambda^0,s^0)$, that satisfies
--   $$\Phi_\rho(x^{k+1},s^{k+1}) \le \Phi_\rho(x^k,s^k) - \delta \quad\text{for all } k = 0,1,2,\dots \qquad (4.8)$$
--   for some $\delta > 0$. Then for every $\epsilon \in (0,1)$ the index
--   $$K = \left\lceil \frac{\Phi_\rho(x^0,s^0)}{\delta} + \frac{\rho-n}{\delta}|\log\epsilon| \right\rceil \qquad (4.9)$$
--   satisfies $\mu_k = (x^k)^Ts^k/n \le \epsilon$ for all $k \ge K$ (4.10).
--
--   This is the generic complexity result of potential-reduction methods: any method that lowers $\Phi_\rho$ by a fixed amount per iteration reaches duality measure $\epsilon$ in $O((\rho-n)|\log\epsilon|)$ iterations, given a bounded starting potential.
--
--   **Formalization Note** The sequence is arbitrary (not tied to a particular algorithm), as in the book. $K$ is the integer ceiling `Int.ceil` of the real expression; it can be negative when $\Phi_\rho(x^0,s^0)$ is very negative, and $k \ge K$ compares the natural number $k$ with it in $\mathbb Z$. $\rho > n$ is the range of the parameter fixed with (4.2).
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 70, Theorem 4.4

import Mathlib
import Definitions.Def_WrightPDIPM_Potential_Setting

open Matrix

namespace WrightPDIPM.Potential

/-- **Theorem 4.4** (Wright, p. 70). Let `ρ > n` (the parameter of (4.2)). Given a starting
point `(x⁰, λ⁰, s⁰) ∈ F°`, suppose an algorithm generates a sequence `(xᵏ, λᵏ, sᵏ) ∈ F°`
that satisfies (4.8), `Φ_ρ(xᵏ⁺¹, sᵏ⁺¹) ≤ Φ_ρ(xᵏ, sᵏ) − δ` for all `k = 0, 1, 2, …`, for some
`δ > 0`. Then for any `ε ∈ (0, 1)`, the index
`K = ⌈Φ_ρ(x⁰, s⁰)/δ + ((ρ − n)/δ)|log ε|⌉` (4.9) satisfies `μ_k ≤ ε` for all `k ≥ K` (4.10).
`K` is an integer (it may be negative); `k ≥ K` compares the natural number `k` with it. -/
theorem theorem_4_4 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (ρ : ℝ) (hρ : (n : ℝ) < ρ)
    (x : ℕ → Fin n → ℝ) (lam : ℕ → Fin m → ℝ) (s : ℕ → Fin n → ℝ)
    (hF : ∀ k, (x k, lam k, s k) ∈ Fo A b c)
    (δ : ℝ) (hδ : 0 < δ)
    (hdec : ∀ k, Phi ρ (x (k + 1)) (s (k + 1)) ≤ Phi ρ (x k) (s k) - δ)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ k : ℕ, ⌈Phi ρ (x 0) (s 0) / δ + (ρ - n) / δ * |Real.log ε|⌉ ≤ (k : ℤ) →
      mu (x k) (s k) ≤ ε := by sorry

end WrightPDIPM.Potential
