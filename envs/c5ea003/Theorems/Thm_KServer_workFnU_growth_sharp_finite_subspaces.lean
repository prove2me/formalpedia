-- Prove2me | Theorems.Thm_KServer_workFnU_growth_sharp_finite_subspaces
-- name    : KServer.workFnU_growth_sharp_finite_subspaces
-- status  : Open
-- author  : @Wenqian Xing
-- created : 2026-09-06T17:40:44.176847+00:00
-- url     : https://prove2.me/theorems/bad018c7-6552-4ac4-bd33-785f989c29de
-- title:
--   Sharp work-function growth uniformly over finite subspaces (open)
-- statement:
--   This is an **open sharp finite-instance bound**. The cited references do not prove its general truth.
--
--   Let $k\ge3$, let $M$ be a metric space with at least $k+3$ distinct points, and fix an initial configuration $C_0$. There should exist one real constant $c$ such that, for every finite subspace $P\subseteq M$ containing $C_0$ and every request sequence $\tau$ in $P$, there are simultaneous majorants $u_t$ of the unordered work-function increments at every injective configuration in $P$, satisfying
--   $$
--   \sum_{t<|\tau|}u_t\le(k+1)\,\mathrm{OPT}_{P}(C_0,\tau)+c.
--   $$
--   Both the work function and the offline cost in this statement are computed in the finite metric $P$. The constant may depend on $k,M,C_0$, but it is chosen before $P$ and $\tau$. A separate constant for each finite metric is insufficient. The initial configuration may contain repeated points, and the ambient space may be infinite and unbounded.
--
--   The proved finite-subspace transfer theorem shows that this finite-instance assertion suffices for `KServer.workFnU_growth_sharp_large`. It leaves the sharp coefficient and the uniform additive constant unresolved; it is not inferred from the known general $2k$ bound.
-- source:
--   Open finite-subspace form of the sharp extended-cost criterion in Koutsoupias (2009), Section 3.4, equation (6), Work-function recurrence in E. Koutsoupias, The k-server problem (2009), Section 3.4, https://users.cs.fiu.edu/~giri/teach/6936/S10/K-Server_CSReviews_09.pdf. The two recurrence inequalities are reused from Shuze Chen's proved formalizations. Finite-support consequence of the recurrence, proved here. Compare the X-lazy schedule observation in Y. Emek, P. Fraigniaud, A. Korman, A. Rosen, On the Additive Constant of the k-server Work Function Algorithm (2009), Section 2, https://arxiv.org/pdf/0902.1378. The exact uniform-constant transfer below is a separate argument.

import Definitions.Def_KServer_workfunctionU
open KServer

theorem KServer.workFnU_growth_sharp_finite_subspaces
    (k : ℕ) (hk : 3 ≤ k) (M : Type) [MetricSpace M] (C₀ : Config k M)
    (hM : ∃ f : Fin (k + 3) → M, Function.Injective f) :
    ∃ c : ℝ, ∀ (P : Finset M) (D₀ : Config k P),
      (∀ i, (D₀ i : M) = C₀ i) → ∀ τ : List P, ∃ u : ℕ → ℝ,
        (∀ t, t < τ.length → ∀ Y : Config k P, Function.Injective Y →
          workFnU D₀ (τ.take (t + 1)) Y ≤ workFnU D₀ (τ.take t) Y + u t) ∧
        (∑ t ∈ Finset.range τ.length, u t) ≤ ((k : ℝ) + 1) * offlineCost D₀ τ + c := by sorry
