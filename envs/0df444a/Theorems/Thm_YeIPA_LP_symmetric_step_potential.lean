-- Prove2me | Theorems.Thm_YeIPA_LP_symmetric_step_potential
-- name    : YeIPA.LP.symmetric_step_potential
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:57:30.975981+00:00
-- url     : https://prove2.me/theorems/f063e8e3-acec-4edb-94b4-916934954006
-- title:
--   Lemma 4.11 — the primal-dual step with $\gamma=n/(n+\rho)$ and step size (4.18) stays interior and lowers $\psi_{n+\rho}$
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have rank $m$, $n\ge1$, $b\ne0$, and let (LP) and (LD) have interior feasible points. Let $(x,y,s)\in\mathring{\mathcal F}$, $\rho\ge0$, and let $d=(d_x,d_y,d_s)$ solve
--   $$Sd_x+Xd_s=\gamma\mu e-Xs,\qquad Ad_x=0,\qquad -A^Td_y-d_s=0\quad(4.17)$$
--   with $\mu=x^Ts/n$ and $\gamma=n/(n+\rho)$. Let $0<\alpha<1$ and
--   $$\theta=\frac{\alpha\sqrt{\min(Xs)}}{\|(XS)^{-1/2}(\frac{x^Ts}{n+\rho}e-Xs)\|}\quad(4.18),$$
--   and $x^+=x+\theta d_x$, $y^+=y+\theta d_y$, $s^+=s+\theta d_s$. Then $(x^+,y^+,s^+)\in\mathring{\mathcal F}$ and
--   $$\psi_{n+\rho}(x^+,s^+)-\psi_{n+\rho}(x,s)\le-\alpha\sqrt{\min(Xs)}\,\Big\|(XS)^{-1/2}\Big(e-\frac{n+\rho}{x^Ts}Xs\Big)\Big\|+\frac{\alpha^2}{2(1-\alpha)}.$$
--
--   Combined with Lemma 4.12 this gives a constant reduction of the primal-dual potential per step of the symmetric primal-dual algorithm (Algorithm 4.4).
--
--   **Formalization Note** $\psi_{n+\rho}(x,s)=(n+\rho)\log(x^Ts)-\sum_j\log(x_js_j)$ with $\rho\ge0$ as defined on p. 121; the book's proof is omitted ("very similar to Lemma 3.12"). The standing assumptions (rank $m$, interior points, p. 63; $b\ne0$, p. 109) and $n\ge1$ are explicit hypotheses. Any solution $d$ of (4.17) is allowed; under the rank assumption it is unique. If the denominator of (4.18) vanishes (only possible for $\rho=0$ at a central point) Lean's $\theta$ is $0$.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 127, Lemma 4.11

import Mathlib
import Definitions.Def_YeIPA_LP_PotentialReduction

open Matrix

namespace YeIPA.LP

/-- Lemma 4.11 (Ye 1997, p. 127). Under the standing assumptions (p. 63), let `(x, y, s) ∈ F̊`,
`ρ ≥ 0` (p. 121), let `d = (d_x, d_y, d_s)` solve (4.17) with `γ = n/(n + ρ)`, let `0 < α < 1`
and `θ = α√min(Xs) / ‖(XS)^{-1/2}((xᵀs/(n + ρ))e − Xs)‖` (4.18), and
`x⁺ = x + θd_x`, `y⁺ = y + θd_y`, `s⁺ = s + θd_s`. Then `(x⁺, y⁺, s⁺) ∈ F̊` and
`ψ_{n+ρ}(x⁺, s⁺) − ψ_{n+ρ}(x, s)
  ≤ −α√min(Xs) ‖(XS)^{-1/2}(e − ((n + ρ)/(xᵀs))Xs)‖ + α²/(2(1 − α))`. -/
theorem symmetric_step_potential {m n : ℕ} (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (hA : StandingAssumptions A b c)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) (hF : IsInteriorFeasible A b c x y s)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ)
    (hd : IsPDDirection A x s ((n : ℝ) / ((n : ℝ) + ρ)) dx dy ds) :
    IsInteriorFeasible A b c (x + pdStepSize ρ α x s • dx) (y + pdStepSize ρ α x s • dy)
        (s + pdStepSize ρ α x s • ds) ∧
      pdPotential ρ (x + pdStepSize ρ α x s • dx) (s + pdStepSize ρ α x s • ds) -
          pdPotential ρ x s ≤
        -α * Real.sqrt (vmin (fun j => x j * s j)) *
            norm2 (fun j => (1 - ((n : ℝ) + ρ) / (x ⬝ᵥ s) * (x j * s j)) /
              Real.sqrt (x j * s j))
          + α ^ 2 / (2 * (1 - α)) := by sorry

end YeIPA.LP
