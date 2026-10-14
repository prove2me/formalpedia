-- Prove2me | Theorems.Thm_KServer_workFnU_growth_sharp_large
-- name    : KServer.workFnU_growth_sharp_large
-- status  : Open
-- author  : @Wenqian Xing
-- created : 2026-09-06T17:09:51.772578+00:00
-- url     : https://prove2.me/theorems/9856f2c5-ac8f-4c3b-a275-8c523d3d9bcc
-- title:
--   Sharp injective total growth beyond the known small cases (open)
-- statement:
--   This is the remaining **open sharp work-function growth assertion**, after separating the established small cases. Its general truth is not supplied by the cited sources.
--
--   Let $k\ge3$, let $M$ be an arbitrary metric space containing at least $k+3$ distinct points, and fix an initial configuration $C_0$. The assertion is that there is one real constant $c$ such that, for every request sequence $\sigma$ of length $m$, there are real numbers $u_0,\ldots,u_{m-1}$ satisfying
--   $$
--   \widehat w_{\sigma_{\le t+1}}(X)-\widehat w_{\sigma_{\le t}}(X)\le u_t
--   \quad(t<m,\ X\text{ injective}),
--   $$
--   $$
--   \sum_{t<m}u_t\le(k+1)\,\mathrm{OPT}(C_0,\sigma)+c.
--   $$
--
--   The numbers $u_t$ may depend on the complete sequence; the constant $c$ may not. The metric need not be finite, bounded, or compact. The sharp coefficient $k+1$ is the sufficient coefficient identified by the Extended Cost Lemma. The proved history-potential equivalence converts such sequence-wise bounds into one potential on all histories. Combined with the established small cases, this would imply `KServer.workFnU_sharp_potential`.
--
--   **Formalization Note** The cardinality hypothesis is the existence of an injective map from `Fin (k + 3)` to $M$. The bound is required only at configurations whose servers occupy distinct points. This is an open assertion, not a proof of the conjecture or an assumed equivalence with competitiveness of every online algorithm.
-- source:
--   Open sharp instance of equation (6) at coefficient k+1 in E. Koutsoupias, The k-server problem (2009), https://users.cs.fiu.edu/~giri/teach/6936/S10/K-Server_CSReviews_09.pdf, Section 3.4, Lemma 2, equation (6), preprint p. 12; potential method pp. 13-15, including Theorems 2-3 and the k+1 and k+2 point cases. K. Brilliantov, E. Bamas, E. Abbe, k-server-bench, https://arxiv.org/html/2604.07240v1, Appendix B.1 Definition 2 and B.2 Theorem 1. The cited results establish the criterion and small cases, not the stated remaining general growth estimate.

import Definitions.Def_KServer_workfunctionU
open KServer

theorem KServer.workFnU_growth_sharp_large
    (k : ℕ) (hk : 3 ≤ k) (M : Type) [MetricSpace M] (C₀ : Config k M)
    (hM : ∃ f : Fin (k + 3) → M, Function.Injective f) :
    ∃ c : ℝ, ∀ σ : List M, ∃ u : ℕ → ℝ,
      (∀ t : ℕ, t < σ.length → ∀ X : Config k M, Function.Injective X →
        workFnU C₀ (σ.take (t + 1)) X ≤ workFnU C₀ (σ.take t) X + u t) ∧
      (∑ t ∈ Finset.range σ.length, u t) ≤ ((k : ℝ) + 1) * offlineCost C₀ σ + c := by sorry
