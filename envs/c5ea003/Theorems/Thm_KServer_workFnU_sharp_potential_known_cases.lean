-- Prove2me | Theorems.Thm_KServer_workFnU_sharp_potential_known_cases
-- name    : KServer.workFnU_sharp_potential_known_cases
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T17:10:18.017107+00:00
-- url     : https://prove2.me/theorems/f462fd8e-e18e-4c25-9dd6-9a2bf6ba3f4d
-- title:
--   Sharp work-function potentials for at most two servers or at most k+2 points
-- statement:
--   Fix $k\ge1$, a metric space $M$, and an initial configuration $C_0$. Suppose either $k\le2$, or $M$ has at most $k+2$ distinct points. Write $\widehat w_l(X)$ for the unordered work function. There exist a real-valued history potential $\Phi$ and a real constant $c$ such that
--   $$
--   \Phi(l)\le(k+1)\,\mathrm{OPT}(C_0,l)+c,
--   $$
--   $$
--   \widehat w_{lr}(X)-\widehat w_l(X)\le\Phi(lr)-\Phi(l)
--   $$
--   for every finite history, next request, and injective configuration $X$.
--
--   This packages the established sharp small cases in the common history-potential interface. The initial configuration may have repeated points, and the constant is fixed for all histories. When $k\le2$, the metric can be infinite or unbounded. This theorem does not assert the general sharp potential for larger server counts and larger metric spaces.
--
--   **Formalization Note** Having at most $k+2$ points is expressed by the absence of an injective map from `Fin (k + 3)` to $M$, so the statement needs no chosen enumeration of $M$.
-- source:
--   History-potential consequences of the established small-case work-function growth results in E. Koutsoupias, The k-server problem (2009), https://users.cs.fiu.edu/~giri/teach/6936/S10/K-Server_CSReviews_09.pdf, Section 3.4, Lemma 2, equation (6), preprint p. 12; potential method pp. 13-15, including Theorems 2-3 and the k+1 and k+2 point cases. K. Brilliantov, E. Bamas, E. Abbe, k-server-bench, https://arxiv.org/html/2604.07240v1, Appendix B.1 Definition 2 and B.2 Theorem 1. The small-case growth theorems are reused from Shuze Chen's proved platform formalizations.

import Definitions.Def_KServer_workfunctionU
open KServer

theorem KServer.workFnU_sharp_potential_known_cases (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M)
    (hsmall : k ≤ 2 ∨ ¬ ∃ f : Fin (k + 3) → M, Function.Injective f) :
    ∃ Φ : List M → ℝ, ∃ c : ℝ,
      (∀ σ : List M, Φ σ ≤ ((k : ℝ) + 1) * offlineCost C₀ σ + c) ∧
      (∀ (l : List M) (r : M) (X : Config k M), Function.Injective X →
        workFnU C₀ (l ++ [r]) X - workFnU C₀ l X ≤ Φ (l ++ [r]) - Φ l) := by sorry
