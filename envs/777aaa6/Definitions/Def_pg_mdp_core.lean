-- Prove2me | Definitions.Def_pg_mdp_core
-- name    : pg_mdp_core
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-05-10T03:39:03.824113+00:00
-- url     : https://prove2.me/theorems/b62e045a-1bf7-476e-8803-c1b3bb6ad2d7
-- statement:
--   Core definitions for the finite-horizon, finite-MDP policy gradient theorem. `pgValue P r π k θ s` is the $k$-step value-to-go $V_k^{\pi_\theta}(s)$ defined by backward recursion ($V_0=0$, $V_{k+1}(s) = \sum_a \pi_\theta(a|s)(r(s,a) + \sum_{s'}P(s'|s,a)V_k(s'))$). `pgQ P r π k θ s a` is the $k$-step action-value $Q_k^{\pi_\theta}(s,a) = r(s,a) + \sum_{s'}P(s'|s,a)V_k(s')$. `pgRho P π t s₀ θ s` is the time-$t$ state visitation probability $\Pr[S_t=s\mid S_0=s_0]$, equal to $(P^\pi)^t_{s_0 s}$, defined by the first-step recursion. The policy parameter $\theta$ is a scalar. No probability axioms (nonnegativity, normalization) are baked in; those appear as hypotheses in theorems.
-- source:
--   R. Sutton, D. McAllester, S. Singh, Y. Mansour. Policy Gradient Methods for Reinforcement Learning with Function Approximation. NeurIPS 1999.

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

/-!
# Finite-horizon MDP value / visitation definitions

Core definitions for the finite-horizon, finite state/action policy gradient theorem.

- `pgValue P r π k θ s`: the `k`-step value-to-go from state `s` under policy `π θ`,
  defined by backward recursion; `pgValue ... 0 _ _ = 0`.
- `pgQ P r π k θ s a`: the `k`-step action-value (`r` + expected next-state value).
- `pgRho P π s₀ t θ s`: the probability of being in state `s` at time `t`, starting
  from `s₀` and following `π θ`, defined by forward recursion.

Parameter `θ : ℝ` is a scalar policy parameter; `π : ℝ → S → A → ℝ` is the parametrized
policy. No probability axioms are baked into the definitions — those are hypotheses of
the theorems that use them.
-/

open Finset

/-- `k`-step value-to-go from state `s`. -/
noncomputable def pgValue {S A : Type} [Fintype S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (π : ℝ → S → A → ℝ) :
    ℕ → ℝ → S → ℝ
  | 0, _, _ => 0
  | (k+1), θ, s => ∑ a : A, π θ s a * (r s a + ∑ s' : S, P s a s' * pgValue P r π k θ s')

/-- `k`-step action-value: reward plus expected next-state `k`-step value. -/
noncomputable def pgQ {S A : Type} [Fintype S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (π : ℝ → S → A → ℝ)
    (k : ℕ) (θ : ℝ) (s : S) (a : A) : ℝ :=
  r s a + ∑ s' : S, P s a s' * pgValue P r π k θ s'

/-- State-visitation distribution: `pgRho P π t s₀ θ s` is the probability of being in
state `s` at time `t`, starting from `s₀` at time `0` and following policy `π θ`.
Defined by *first-step* recursion (peel off the initial transition); this is exactly
`(P^π)ᵗ s₀ s` where `P^π s s' = ∑_a π θ s a · P s a s'`. -/
noncomputable def pgRho {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]
    (P : S → A → S → ℝ) (π : ℝ → S → A → ℝ) :
    ℕ → S → ℝ → S → ℝ
  | 0, s₀, _, s => if s = s₀ then 1 else 0
  | (t+1), s₀, θ, s => ∑ s' : S, (∑ a : A, π θ s₀ a * P s₀ a s') * pgRho P π t s' θ s

section UnfoldLemmas

variable {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]
variable (P : S → A → S → ℝ) (r : S → A → ℝ) (π : ℝ → S → A → ℝ)

lemma pgValue_zero (θ : ℝ) (s : S) : pgValue P r π 0 θ s = 0 := rfl

lemma pgValue_succ (k : ℕ) (θ : ℝ) (s : S) :
    pgValue P r π (k+1) θ s = ∑ a : A, π θ s a * pgQ P r π k θ s a := rfl

lemma pgQ_def (k : ℕ) (θ : ℝ) (s : S) (a : A) :
    pgQ P r π k θ s a = r s a + ∑ s' : S, P s a s' * pgValue P r π k θ s' := rfl

lemma pgRho_zero (s₀ : S) (θ : ℝ) (s : S) :
    pgRho P π 0 s₀ θ s = if s = s₀ then 1 else 0 := rfl

lemma pgRho_succ (t : ℕ) (s₀ : S) (θ : ℝ) (s : S) :
    pgRho P π (t+1) s₀ θ s
      = ∑ s' : S, (∑ a : A, π θ s₀ a * P s₀ a s') * pgRho P π t s' θ s := rfl

end UnfoldLemmas


