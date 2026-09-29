-- Prove2me | Theorems.Thm_pg_rho_forward_recursion
-- name    : pg_rho_forward_recursion
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-10T04:25:54.83174+00:00
-- url     : https://prove2.me/theorems/45028f32-8270-45b4-bd2e-dfab682312b4
-- statement:
--   Chapman–Kolmogorov / semigroup property for `pgRho`: the first-step recursion used to *define* `pgRho` agrees with the last-step (forward) recursion $\rho_{t+1}(s_0,s) = \sum_{s'}\rho_t(s_0,s')\,p^\pi(s',s)$, i.e. both compute $(P^\pi)^t_{s_0,s}$. This validates that `pgRho t s₀ θ s` really is $\Pr[S_t=s\mid S_0=s_0]$ in the usual sense. Proof: induction on $t$.
-- source:
--   Standard Markov chain theory (Chapman-Kolmogorov).

import Definitions.Def_pg_mdp_core
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

theorem pg_rho_forward_recursion {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]
    (P : S → A → S → ℝ) (π : ℝ → S → A → ℝ) (θ : ℝ) :
    ∀ (t : ℕ) (s₀ s : S), pgRho P π (t + 1) s₀ θ s
      = ∑ s' : S, pgRho P π t s₀ θ s' * ∑ a : A, π θ s' a * P s' a s := by sorry
