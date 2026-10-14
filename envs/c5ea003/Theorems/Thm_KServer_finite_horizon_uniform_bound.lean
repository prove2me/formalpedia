-- Prove2me | Theorems.Thm_KServer_finite_horizon_uniform_bound
-- name    : KServer.finite_horizon_uniform_bound
-- status  : Open
-- author  : @Wenqian Xing
-- created : 2026-09-06T07:10:35.432991+00:00
-- url     : https://prove2.me/theorems/10ab1333-61a5-4d90-ac6b-b692e2316d1e
-- title:
--   The k-server conjecture on finite request sets and horizons, with a uniform additive constant
-- statement:
--   Fix $k\ge1$, an arbitrary metric space $M$, and an initial configuration $C_0$ of $k$ labeled servers. There is a real constant $a$ such that, for every finite set of allowed requests $P\subseteq M$ and every natural horizon $n$, some deterministic online algorithm $A_{P,n}$ starts at $C_0$ and satisfies
--
--   $$
--   \operatorname{cost}_{A_{P,n}}(\sigma)
--   \le k\,\operatorname{OPT}(C_0,\sigma)+a
--   \qquad\text{for every }\sigma\in P^{\le n}.
--   $$
--
--   The algorithm may depend on $P$ and $n$, but the additive constant may depend only on the previously fixed data. In particular, the quantifiers are
--
--   $$
--   \exists a\;\forall P\text{ finite}\;\forall n\;\exists A_{P,n}.
--   $$
--
--   All algorithms satisfy the usual service constraint on every history; the cost guarantee is required only on the indicated finite collection of sequences. The offline optimum is the mission's existing optimum in $M$, with the same initial configuration.
--
--   This is an open, equivalent finite-game formulation of the deterministic k-server conjecture. A compactness reduction turns these uniform finite-game guarantees into one globally competitive algorithm. The uniform additive bound is the unresolved content: allowing $a$ to depend on the request set or the horizon would give a different, insufficient statement.
-- source:
--   Original equivalent finite-game reformulation of KServer.kserver_conjecture (70112b3b-59e8-4650-bb90-a754675dea88), via KServer.online_cost_compactness. Source conjecture: Koutsoupias, The k-server problem (2009), Conjecture 1, preprint p. 2, https://www.cs.ox.ac.uk/people/elias.koutsoupias/Personal/Papers/paper-kou09.pdf; original modern conjecture: Koutsoupias-Papadimitriou (1995), Conjecture 1.1, https://doi.org/10.1145/210118.210128. This finite-game assertion remains open; it is not asserted to be a known theorem in either reference.

import Definitions.Def_KServer_model
open KServer

theorem KServer.finite_horizon_uniform_bound
    (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] (C₀ : Config k M) :
    ∃ a : ℝ, ∀ P : Finset M, ∀ n : ℕ,
      ∃ A : OnlineAlgorithm k M, A.conf [] = C₀ ∧
        ∀ σ : List M, σ.length ≤ n → (∀ r ∈ σ, r ∈ P) →
          A.cost σ ≤ (k : ℝ) * offlineCost C₀ σ + a := by sorry
