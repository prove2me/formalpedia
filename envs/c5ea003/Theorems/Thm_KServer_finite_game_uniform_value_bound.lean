-- Prove2me | Theorems.Thm_KServer_finite_game_uniform_value_bound
-- name    : KServer.finite_game_uniform_value_bound
-- status  : Open
-- author  : @Wenqian Xing
-- created : 2026-09-06T15:19:19.166494+00:00
-- url     : https://prove2.me/theorems/6ac76887-fda3-48aa-a3f3-138bfb12b5e4
-- title:
--   Open uniform bound for the competitive finite-game values
-- statement:
--   Fix $k\ge1$, an arbitrary metric space $M$, and an initial configuration $C_0$. In the finite stopping-game recursion, take
--
--   $$b(\sigma)=k\operatorname{OPT}(C_0,\sigma).$$
--
--   The conjecture is that its initial values have one common real upper bound:
--
--   $$\exists a\in\mathbb R\ \forall P\subseteq M\text{ finite}\ \forall n\in\mathbb N,\qquad V_n^{P,b}(\varnothing,C_0)\le a.$$
--
--   The constant may depend on $k$, $M$, and $C_0$, but on neither the finite request set nor the horizon. The offline optimum is computed in the original ambient metric space from the same initial configuration.
--
--   This is an open scalar formulation of `KServer.finite_horizon_uniform_bound`, using the exact minimax characterization. It is not a proved estimate: the unresolved content is a uniform bound on the iterates of the explicit max-min recursion. A finite value for each individual game, or monotonicity in the horizon, does not establish this assertion.
-- source:
--   Original backward-induction formulation for KServer.finite_horizon_uniform_bound (10ab1333-61a5-4d90-ac6b-b692e2316d1e). The game recursion is specified in this definition, and its exact algorithmic interpretation is proved in KServer.finite_game_characterization. Source of the underlying open conjecture: Koutsoupias, The k-server problem (2009), Conjecture 1, preprint p. 2, https://www.cs.ox.ac.uk/people/elias.koutsoupias/Personal/Papers/paper-kou09.pdf. This recurrence and characterization are an original formal development, not a claim that the conjecture is proved in that reference.

import Definitions.Def_KServer_finite_game
open KServer

theorem KServer.finite_game_uniform_value_bound
    (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] (C₀ : Config k M) :
    ∃ a : ℝ, ∀ P : Finset M, ∀ n : ℕ,
      finiteGameValue hk P (fun σ => (k : ℝ) * offlineCost C₀ σ) n [] C₀ ≤ a := by sorry
