-- Prove2me | Theorems.Thm_KServer_workFnU_sharp_potential
-- name    : KServer.workFnU_sharp_potential
-- status  : Open
-- author  : @Wenqian Xing
-- created : 2026-09-06T16:48:01.397+00:00
-- url     : https://prove2.me/theorems/239a6d8d-9070-46f7-b56d-c9a7c1e8a379
-- title:
--   Sharp work-function potential: an open sufficient condition
-- statement:
--   This is an **open sufficient condition** for the sharp $k$-server bound, expressed through work-function growth. Existence of the potential in this statement is conjectural in this generality; the cited sources establish the conditional potential method, not this general existence assertion.
--
--   Fix $k\ge1$, an arbitrary metric space $M$, and an initial configuration $C_0$. Write $\widehat w_l(X)$ for the unordered work function after a finite request history $l$. The problem is to establish the existence of a real-valued function $\Phi$ on histories and a real constant $c$ such that
--   $$
--   \Phi(l)\le(k+1)\,\mathrm{OPT}(C_0,l)+c
--   $$
--   for every finite history, and
--   $$
--   \widehat w_{l r}(X)-\widehat w_l(X)
--   \le\Phi(l r)-\Phi(l)
--   $$
--   for every history $l$, next request $r$, and injective configuration $X$.
--
--   Both $\Phi$ and $c$ may depend on $k,M,C_0$, but they must be chosen once for all histories. In particular, there is no dependence on a finite request alphabet or on a horizon. The coefficient $k+1$ is the sharp total-growth coefficient sought through the Extended Cost Lemma. Together with the proved potential-to-game implication, this condition would imply `KServer.finite_game_uniform_value_bound`. It is a work-function sufficient condition, not an asserted equivalence with existence of an arbitrary $k$-competitive algorithm.
--
--   **Formalization Note** A configuration is injective when its servers occupy distinct points. No finiteness, boundedness, compactness, or minimum-attainment hypothesis on the metric is imposed. A potential depending only on the work function is a special case of the history-indexed function allowed here.
-- source:
--   Conjectural sufficient condition motivated by E. Koutsoupias, The k-server problem, Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.4, Lemma 2, equation (6), and the paragraph immediately after its statement identifying coefficient k+1 as sufficient; preprint pp. 12-14, https://users.cs.fiu.edu/~giri/teach/6936/S10/K-Server_CSReviews_09.pdf. Potential criterion: K. Brilliantov, E. Bamas, E. Abbe, k-server-bench, https://arxiv.org/html/2604.07240v1, Appendix B.2, Theorem 1. The references prove the conditional criterion, not existence of a sharp potential in arbitrary metrics. The injective arbitrary-metric formulation follows the proved platform theorem KServer.extended_cost_lemma_injective.

import Definitions.Def_KServer_workfunctionU
open KServer

theorem KServer.workFnU_sharp_potential
    (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] (C₀ : Config k M) :
    ∃ Φ : List M → ℝ, ∃ c : ℝ,
      (∀ σ : List M, Φ σ ≤ ((k : ℝ) + 1) * offlineCost C₀ σ + c) ∧
      (∀ (l : List M) (r : M) (X : Config k M), Function.Injective X →
        workFnU C₀ (l ++ [r]) X - workFnU C₀ l X ≤ Φ (l ++ [r]) - Φ l) := by sorry
