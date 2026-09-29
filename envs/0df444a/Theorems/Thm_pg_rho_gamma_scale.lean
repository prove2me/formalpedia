-- Prove2me | Theorems.Thm_pg_rho_gamma_scale
-- name    : pg_rho_gamma_scale
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-10T05:05:21.124348+00:00
-- url     : https://prove2.me/theorems/df0e2c02-1094-4dba-877c-9eb6391e24d2
-- statement:
--   Discounting the transition kernel scales the visitation weight by $\gamma^t$: $\rho_t^{\gamma P}(s\mid s_0) = \gamma^t\,\rho_t^P(s\mid s_0)$. This is the key lemma for specializing `policy_gradient_finite_horizon` to the discounted setting via the substitution $P \leftarrow \gamma P$. Proof: induction on $t$.
-- source:
--   Elementary; used to derive the discounted PGT from the undiscounted one.

import Definitions.Def_pg_mdp_core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

theorem pg_rho_gamma_scale {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]
    (P : S → A → S → ℝ) (π : ℝ → S → A → ℝ) (θ : ℝ) (γ : ℝ) :
    ∀ (t : ℕ) (s₀ s : S),
      pgRho (fun s a s' => γ * P s a s') π t s₀ θ s = γ ^ t * pgRho P π t s₀ θ s := by sorry
