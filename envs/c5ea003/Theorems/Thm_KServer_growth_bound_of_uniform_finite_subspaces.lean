-- Prove2me | Theorems.Thm_KServer_growth_bound_of_uniform_finite_subspaces
-- name    : KServer.growth_bound_of_uniform_finite_subspaces
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T17:40:41.39811+00:00
-- url     : https://prove2.me/theorems/d8009dc7-8235-4730-a3b0-39a0f55b45c4
-- title:
--   Transfer uniform work-function growth bounds from finite subspaces
-- statement:
--   Fix $k\ge1$, an arbitrary metric space $M$, an initial configuration $C_0$, and real numbers $a>0$ and $c$. Assume there exists an injective $k$-server configuration in $M$.
--
--   Suppose that for every finite subset $P\subseteq M$ containing the initial configuration, and every request sequence $\tau$ in $P$, the work function computed entirely in $P$ admits majorants of its injective increments whose sum is at most
--   $$
--   a\,\mathrm{OPT}_{P}(C_0,\tau)+c.
--   $$
--   The same constants $a,c$ must work for all such $P$ and $\tau$.
--
--   Then every finite request sequence $\sigma$ in $M$ admits majorants of all its injective work-function increments whose sum is at most
--   $$
--   a\,\mathrm{OPT}_{M}(C_0,\sigma)+c.
--   $$
--   The target includes configurations using points outside the request sequence. No boundedness or compactness assumption on $M$, existence of an optimal schedule, or attainment of maximal increments is imposed. The proof places finitely many selected terminal configurations and any feasible schedule into a common finite subspace, applies the finite bound, then takes an infimum over schedules and finite sums of suprema over terminal configurations. Constants depending on $P$ do not meet the hypothesis.
-- source:
--   Finite-support consequence of the recurrence, proved here. Compare the X-lazy schedule observation in Y. Emek, P. Fraigniaud, A. Korman, A. Rosen, On the Additive Constant of the k-server Work Function Algorithm (2009), Section 2, https://arxiv.org/pdf/0902.1378. The exact uniform-constant transfer below is a separate argument.

import Definitions.Def_KServer_workfunctionU
open KServer

theorem KServer.growth_bound_of_uniform_finite_subspaces (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (a c : ℝ) (ha : 0 < a)
    (hI : ∃ X : Config k M, Function.Injective X)
    (H : ∀ (P : Finset M) (D₀ : Config k P),
      (∀ i, (D₀ i : M) = C₀ i) → ∀ τ : List P, ∃ u : ℕ → ℝ,
        (∀ t, t < τ.length → ∀ Y : Config k P, Function.Injective Y →
          workFnU D₀ (τ.take (t + 1)) Y ≤ workFnU D₀ (τ.take t) Y + u t) ∧
        (∑ t ∈ Finset.range τ.length, u t) ≤ a * offlineCost D₀ τ + c) :
    ∀ σ : List M, ∃ u : ℕ → ℝ,
      (∀ t, t < σ.length → ∀ X : Config k M, Function.Injective X →
        workFnU C₀ (σ.take (t + 1)) X ≤ workFnU C₀ (σ.take t) X + u t) ∧
      (∑ t ∈ Finset.range σ.length, u t) ≤ a * offlineCost C₀ σ + c := by sorry
