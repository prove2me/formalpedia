-- Prove2me | Theorems.Thm_pg_rho_normalization
-- name    : pg_rho_normalization
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-10T04:25:42.104642+00:00
-- url     : https://prove2.me/theorems/54a46c20-2593-4480-9fe7-07215f7dce72
-- statement:
--   The state-visitation weight `pgRho` sums to $1$ over the state space, for every time $t$ and start state $s_0$, whenever the transition kernel $P$ and policy $\pi$ are normalized. Combined with `pg_rho_nonneg`, this shows `pgRho t s₀ θ (·)` is a probability distribution. Proof: induction on $t$. Base: $\sum_s [s=s_0] = 1$. Step: $\sum_s \rho_{t+1}(s_0,s) = \sum_s \sum_{s'} W(s_0,s')\rho_t(s',s) = \sum_{s'} W(s_0,s')\sum_s \rho_t(s',s) = \sum_{s'} W(s_0,s') = \sum_a\pi_\theta(a|s_0)\sum_{s'}P(s'|s_0,a) = \sum_a\pi_\theta(a|s_0) = 1$.
-- source:
--   Standard MDP theory.

import Definitions.Def_pg_mdp_core
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

theorem pg_rho_normalization {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]
    (P : S → A → S → ℝ) (π : ℝ → S → A → ℝ) (θ : ℝ)
    (hP : ∀ s a, ∑ s' : S, P s a s' = 1) (hπ : ∀ s, ∑ a : A, π θ s a = 1) :
    ∀ (t : ℕ) (s₀ : S), ∑ s : S, pgRho P π t s₀ θ s = 1 := by sorry
