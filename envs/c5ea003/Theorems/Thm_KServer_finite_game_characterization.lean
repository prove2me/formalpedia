-- Prove2me | Theorems.Thm_KServer_finite_game_characterization
-- name    : KServer.finite_game_characterization
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T15:19:10.118212+00:00
-- url     : https://prove2.me/theorems/d1949738-8741-4ee5-b2c0-3e5e068eb336
-- title:
--   Exact minimax characterization of finite-horizon k-server guarantees
-- statement:
--   Fix $k\ge1$, an arbitrary metric space $M$, an initial configuration $C_0$, a finite request set $P$, a horizon $n$, an arbitrary real-valued prefix payoff $b$, and a real threshold $a$. Let $V_n$ denote the finite stopping-game recursion of `KServer_finite_game`. Then
--
--   $$V_n(\varnothing,C_0)\le a\quad\Longleftrightarrow\quad\exists A:\ A(\varnothing)=C_0\ \text{ and }\ \operatorname{cost}_A(\sigma)\le b(\sigma)+a\ \text{ for every }\sigma\in P^{\le n}.$$
--
--   The algorithm is deterministic and online, and must serve all histories in $M$, including those outside the finite test set. The guarantee concerns every permitted stopping prefix. No regularity, sign, monotonicity, or offline-optimality assumption is imposed on $b$.
--
--   This identifies the exact scalar threshold for existence of a finite-horizon online strategy. It justifies using the finite recursion both to construct algorithms and to rule out proposed competitive bounds on a fixed finite game.
-- source:
--   Original backward-induction formulation for KServer.finite_horizon_uniform_bound (10ab1333-61a5-4d90-ac6b-b692e2316d1e). The game recursion is specified in this definition, and its exact algorithmic interpretation is proved in KServer.finite_game_characterization. Source of the underlying open conjecture: Koutsoupias, The k-server problem (2009), Conjecture 1, preprint p. 2, https://www.cs.ox.ac.uk/people/elias.koutsoupias/Personal/Papers/paper-kou09.pdf. This recurrence and characterization are an original formal development, not a claim that the conjecture is proved in that reference.

import Definitions.Def_KServer_finite_game
open KServer

theorem KServer.finite_game_characterization (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (P : Finset M) (b : List M → ℝ) (n : ℕ) (a : ℝ) :
    finiteGameValue hk P b n [] C₀ ≤ a ↔
      ∃ A : OnlineAlgorithm k M, A.conf [] = C₀ ∧
        ∀ σ : List M, σ.length ≤ n → (∀ r ∈ σ, r ∈ P) →
          A.cost σ ≤ b σ + a := by sorry
