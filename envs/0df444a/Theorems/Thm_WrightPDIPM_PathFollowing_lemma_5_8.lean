-- Prove2me | Theorems.Thm_WrightPDIPM_PathFollowing_lemma_5_8
-- name    : WrightPDIPM.PathFollowing.lemma_5_8
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:54:06.025308+00:00
-- url     : https://prove2.me/theorems/7bfa44fc-e3f8-4c00-8514-9a18da296cda
-- title:
--   Lemma 5.8 — the corrector step returns N₂(0.5) to N₂(0.25) with μ unchanged
-- statement:
--   Let $A, b, c$ be LP data, let $(x,\lambda,s) \in \mathcal N_2(0.5)$, and let $(\Delta x, \Delta\lambda, \Delta s)$ solve the step equations (1.12) at this point with $\sigma = 1$ (the centering direction). Then the full step satisfies
--   $$(x + \Delta x, \lambda + \Delta\lambda, s + \Delta s) \in \mathcal N_2(0.25), \qquad \mu(1) = \mu,$$
--   where $\mu(1) = (x + \Delta x)^{\mathsf T}(s + \Delta s)/n$ and $\mu = x^{\mathsf T}s/n$.
--
--   This is the corrector half of the predictor-corrector method: it restores centrality without changing the duality measure.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 95, Lemma 5.8

import Mathlib
import Definitions.Def_WrightPDIPM_PathFollowing_Setup

namespace WrightPDIPM.PathFollowing

/-- Lemma 5.8 (p. 95): if `(x, λ, s) ∈ N₂(0.5)` and `(Δx, Δλ, Δs)` solves (1.12) with σ = 1,
then `(x(1), λ(1), s(1)) = (x + Δx, λ + Δλ, s + Δs) ∈ N₂(0.25)` and `μ(1) = μ`. -/
theorem lemma_5_8 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ) (hN : (x, lam, s) ∈ N2 A b c (1 / 2))
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ)
    (hstep : IsStep A x s 1 dx dlam ds) :
    (x + dx, lam + dlam, s + ds) ∈ N2 A b c (1 / 4) ∧ mu (x + dx) (s + ds) = mu x s := by sorry

end WrightPDIPM.PathFollowing
