-- Prove2me | Theorems.Thm_KServer_workFnU_initial_stability
-- name    : KServer.workFnU_initial_stability
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T23:11:56.683078+00:00
-- url     : https://prove2.me/theorems/956e5e44-699f-4b68-b968-891ce4f81700
-- title:
--   Stability under changes of the initial configuration
-- statement:
--   Let $k\ge1$ and let $A,B$ be labelled initial configurations in any metric space. For every finite request sequence $\sigma$,
--   $$
--   |\widehat w_{A,\sigma}(X)-\widehat w_{B,\sigma}(X)|\le \sum_i d(A_i,B_i)
--   $$
--   for every terminal configuration $X$, and
--   $$
--   |\mathrm{OPT}(A,\sigma)-\mathrm{OPT}(B,\sigma)|\le \sum_i d(A_i,B_i).
--   $$
--   The bound is independent of the history length. Configurations may have repeated points, and the metric space need not be finite, bounded, or compact. The labelled backward recurrence transports the movement-cost triangle inequality from the empty history to every history. Taking the finite minimum over terminal permutations gives the unordered bound. Approximate offline endpoints then give the offline bound without assuming an optimal schedule exists.
-- source:
--   A direct consequence of the standard work-function recurrence in E. Koutsoupias, The k-server problem (2009), Section 3.4, https://users.cs.fiu.edu/~giri/teach/6936/S10/K-Server_CSReviews_09.pdf. The recurrence and approximate-endpoint formalizations are credited to Shuze Chen; this initial-stability consequence is proved here.

import Definitions.Def_KServer_workfunctionU
open KServer

theorem KServer.workFnU_initial_stability (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (A B : Config k M) (σ : List M) :
    (∀ X : Config k M, |workFnU A σ X - workFnU B σ X| ≤ moveCost A B) ∧
      |offlineCost A σ - offlineCost B σ| ≤ moveCost A B := by sorry
