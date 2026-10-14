-- Prove2me | Theorems.Thm_KServer_workFnU_growth_sharp_coalesced_finite
-- name    : KServer.workFnU_growth_sharp_coalesced_finite
-- status  : Open
-- author  : @Wenqian Xing
-- created : 2026-09-06T23:12:19.653845+00:00
-- url     : https://prove2.me/theorems/5e15a9b5-13e1-43a2-b284-0d3be0819bd3
-- title:
--   Sharp injective growth from a coalesced start on a finite metric (open)
-- statement:
--   This is an **open sharp inequality**, not an established consequence of the cited references.
--
--   Let $k\ge3$, let $N$ be any finite metric space, and start all servers at one point $p$. For every finite request sequence $\sigma$, there should be simultaneous majorants $u_t$ of all unordered work-function increments at injective terminal configurations, with
--   $$
--   \sum_{t<|\sigma|}u_t\le(k+1)\,\mathrm{OPT}(p^k,\sigma).
--   $$
--   There is no additive constant. The initial configuration is coalesced, while the tested terminal configurations are injective. The quantification includes arbitrary finite metrics, not just trees, cycles, or uniform metrics.
--
--   This is a sufficient hard child for the uniform finite-subspace target. A forcing prefix and initial-configuration perturbation would turn this strict coalesced estimate into the explicit arbitrary-start additive constant
--   $$
--   (k+1)\sum_i d(C_0(0),C_0(i)).
--   $$
--   The general sharp coefficient remains unproved here. Exact finite-state checks of two particular six-point metrics are only computational evidence for those instances. They do not justify this universal statement. Replacing the coalesced initial configuration by an arbitrary one makes the zero-additive claim false; it is essential to the proposed reduction.
-- source:
--   Proposed coalesced-start sufficient form of the open sharp extended-cost criterion in E. Koutsoupias, The k-server problem (2009), Section 3.4, https://users.cs.fiu.edu/~giri/teach/6936/S10/K-Server_CSReviews_09.pdf, equation (6). Neither that reference nor Y. Emek, P. Fraigniaud, A. Korman and A. Rosen, On the Additive Constant of the k-server Work Function Algorithm (2009), Section 3, Lemma 3.3 and Corollary 3.5, https://arxiv.org/pdf/0902.1378 proves this general strict inequality.

import Definitions.Def_KServer_workfunctionU
open KServer

theorem KServer.workFnU_growth_sharp_coalesced_finite
    (k : ℕ) (hk : 3 ≤ k) (M : Type) [MetricSpace M] [Fintype M]
    (p : M) (τ : List M) :
    ∃ u : ℕ → ℝ,
      (∀ t, t < τ.length → ∀ Y : Config k M, Function.Injective Y →
        workFnU (fun _ => p) (τ.take (t + 1)) Y ≤
          workFnU (fun _ => p) (τ.take t) Y + u t) ∧
      (∑ t ∈ Finset.range τ.length, u t) ≤
        ((k : ℝ) + 1) * offlineCost (fun _ : Fin k => p) τ := by sorry
