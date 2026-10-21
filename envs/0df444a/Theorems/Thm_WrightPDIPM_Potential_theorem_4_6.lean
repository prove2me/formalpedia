-- Prove2me | Theorems.Thm_WrightPDIPM_Potential_theorem_4_6
-- name    : WrightPDIPM.Potential.theorem_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:53:13.673494+00:00
-- url     : https://prove2.me/theorems/ef13dd50-11ba-49b1-9bab-5fbe2d242475
-- title:
--   Theorem 4.6 — with τ = 0.5 and ᾱ = v_min/(2‖r‖), q(ᾱ) − q(0) ≤ −0.15, so each PR step lowers Φ_ρ by 0.15
-- statement:
--   Let $n \ge 1$, $A \in \mathbb R^{m\times n}$, $b \in \mathbb R^m$, $c \in \mathbb R^n$, and let $(x,\lambda,s)$ be strictly feasible: $Ax = b$, $A^T\lambda + s = c$, $x > 0$, $s > 0$. Let $\rho \ge n + \sqrt n$ and $\mu = x^Ts/n$, and let $(\Delta x,\Delta\lambda,\Delta s)$ be the search direction of Algorithm PR, the solution of
--   $$A\Delta x = 0,\quad A^T\Delta\lambda + \Delta s = 0,\quad S\Delta x + X\Delta s = -XSe + \frac n\rho\mu e.$$
--   Let $\tau = 0.5$, let $q(\alpha) = \Phi_\rho(x,s) + \alpha g_1 + \frac12\alpha^2g_2$ be the quadratic estimate (4.18) of the potential $\Phi_\rho(x,s) = \rho\log x^Ts - \sum_i\log x_is_i$ along the direction, with $g_1, g_2$ as in (4.17), and define, with $v_{\min} = \min_i (x_is_i)^{1/2}$ and $r = -v + \frac n\rho\mu V^{-1}e$,
--   $$\bar\alpha = \frac{v_{\min}}{2\|r\|}. \qquad (4.31)$$
--   Then
--   1. $q(\bar\alpha) - q(0) \le -0.15$; and
--   2. (4.8) holds with $\delta = 0.15$: if $\alpha_{\max} = \sup\{\alpha\in[0,1] : (x,s)+\alpha(\Delta x,\Delta s)\ge0\}$ and $\alpha_k \in (0,\alpha_{\max})$ minimizes $\alpha\mapsto\Phi_\rho(x+\alpha\Delta x, s+\alpha\Delta s)$ over $(0,\alpha_{\max})$, as in step (4.6) of Algorithm PR, then
--   $$\Phi_\rho(x+\alpha_k\Delta x, s+\alpha_k\Delta s) \le \Phi_\rho(x,s) - 0.15.$$
--
--   This is the per-iteration guarantee of the Kojima–Mizuno–Yoshise potential-reduction method; with Theorem 4.4 it gives the $O(\sqrt n|\log\epsilon|)$ iteration bound at $\rho = n + \sqrt n$.
--
--   **Formalization Note** The hypothesis $\rho \ge n + \sqrt n$ is not printed in Theorem 4.6; it is the standing hypothesis of Lemma 4.5 to Corollary 4.7 (pp. 75–78), the book's proof uses it through (4.28), and without it the theorem is false (finding F1, posed as `theorem_4_6_probe`). $n \ge 1$ is implicit in the book. Part 2 is stated for every minimizer rather than asserting one exists, since a minimizer over the open interval need not exist. $\bar\alpha$ is formed with Lean's division; $r \ne 0$ under the hypotheses (because $\rho > n$), so no junk value $x/0 = 0$ arises. $q$ uses $\tau = 1/2$; $0.15$ is written $15/100$.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 76, Theorem 4.6

import Mathlib
import Definitions.Def_WrightPDIPM_Potential_Setting

open Matrix

namespace WrightPDIPM.Potential

/-- **Theorem 4.6** (Wright, p. 76). Let `n ≥ 1`, `(x, λ, s) ∈ F°`, `ρ ≥ n + √n` (the
standing hypothesis of Lemma 4.5 – Corollary 4.7, used by the proof through (4.28)), and let
`(Δx, Δλ, Δs)` be the direction of Algorithm PR, i.e. the solution of (4.12) and (4.19).
Let `τ = 0.5` and `ᾱ = v_min/(2‖r‖)` (4.31). Then
(a) `q(ᾱ) − q(0) ≤ −0.15`, with `q` the quadratic estimate (4.18) for `τ = 0.5`; and
(b) (4.8) holds with `δ = 0.15`: every step length `α_k ∈ (0, α_max)` that minimizes
`α ↦ Φ_ρ(x + αΔx, s + αΔs)` over `(0, α_max)` (4.6) gives
`Φ_ρ(x + α_kΔx, s + α_kΔs) ≤ Φ_ρ(x, s) − 0.15`. -/
theorem theorem_4_6 {m n : ℕ} (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ)
    (hF : (x, lam, s) ∈ Fo A b c) (ρ : ℝ) (hρ : (n : ℝ) + Real.sqrt n ≤ ρ)
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ)
    (hdir : IsPRDirection A ρ x s dx dlam ds) :
    q ρ (1 / 2) x s dx ds (alphaBar ρ x s) - q ρ (1 / 2) x s dx ds 0 ≤ -(15 / 100 : ℝ) ∧
      ∀ αk ∈ Set.Ioo 0 (alphaMax x s dx ds),
        IsMinOn (fun α : ℝ => Phi ρ (x + α • dx) (s + α • ds))
            (Set.Ioo 0 (alphaMax x s dx ds)) αk →
          Phi ρ (x + αk • dx) (s + αk • ds) ≤ Phi ρ x s - 15 / 100 := by sorry

end WrightPDIPM.Potential
