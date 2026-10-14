-- Prove2me | Theorems.Thm_KServer_finite_game_bound_of_work_potential
-- name    : KServer.finite_game_bound_of_work_potential
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T16:48:10.992674+00:00
-- url     : https://prove2.me/theorems/073f9ec1-f5db-41d3-9e4d-94611810bf92
-- title:
--   A work-function potential bounds every finite k-server game
-- statement:
--   Let $k\ge 1$, let $M$ be any metric space, and fix an initial configuration $C_0$. Write $\widehat w_l(X)$ for the unordered work function after history $l$, and write $V_{P,n}^{\rho}$ for the finite game value with stopping payoff $-\rho\,\mathrm{OPT}(C_0,l)$.
--
--   Suppose $\rho\ge0$ and there are a real-valued function $\Phi$ on finite request histories and a real constant $c$ such that
--   $$
--   \Phi(l)\le(\rho+1)\,\mathrm{OPT}(C_0,l)+c
--   $$
--   for every history, and
--   $$
--   \widehat w_{l r}(X)-\widehat w_l(X)\le\Phi(l r)-\Phi(l)
--   $$
--   for every history $l$, next request $r$, and configuration $X$ whose servers occupy distinct points. Then
--   $$
--   \exists a\in\mathbb R\quad\forall P\subseteq M\text{ finite}\quad\forall n\in\mathbb N,
--   \qquad V_{P,n}^{\rho}(\varnothing,C_0)\le a.
--   $$
--
--   This is the work-function potential criterion applied to the finite game formulation. It isolates the construction of the potential from the conversion to one bound for all finite request alphabets and horizons. No finiteness, boundedness, compactness, or attainment assumption on $M$ is imposed. The potential and its upper-bound constant are hypotheses, rather than assertions that such a potential exists for a specified competitive ratio.
--
--   **Formalization Note** The history-indexed potential may depend on the entire history. Increments are required only at injective configurations, matching the existing injective extended-cost theorem. Spaces too small to admit an injective configuration are covered by the existing covering-configuration theorem.
-- source:
--   Application of the work-function potential criterion: E. Koutsoupias, The k-server problem (2009), Section 3.4, Lemma 2, equation (6), and potential discussion, preprint pp. 12-14, https://users.cs.fiu.edu/~giri/teach/6936/S10/K-Server_CSReviews_09.pdf; K. Brilliantov, E. Bamas, E. Abbe, k-server-bench, https://arxiv.org/html/2604.07240v1, Appendix B.2, Theorem 1. Finite-game conclusion uses the proved platform theorem KServer.finite_game_characterization.

import Definitions.Def_KServer_finite_game
import Definitions.Def_KServer_workfunctionU
open KServer

theorem KServer.finite_game_bound_of_work_potential (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (ρ : ℝ) (hρ : 0 ≤ ρ) (Φ : List M → ℝ) (c : ℝ)
    (hupper : ∀ σ : List M, Φ σ ≤ (ρ + 1) * offlineCost C₀ σ + c)
    (hstep : ∀ (l : List M) (r : M) (X : Config k M), Function.Injective X →
      workFnU C₀ (l ++ [r]) X - workFnU C₀ l X ≤ Φ (l ++ [r]) - Φ l) :
    ∃ a : ℝ, ∀ P : Finset M, ∀ n : ℕ,
      finiteGameValue hk P (fun σ => ρ * offlineCost C₀ σ) n [] C₀ ≤ a := by sorry
