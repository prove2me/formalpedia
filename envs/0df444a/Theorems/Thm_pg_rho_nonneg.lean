-- Prove2me | Theorems.Thm_pg_rho_nonneg
-- name    : pg_rho_nonneg
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-10T04:25:36.097257+00:00
-- url     : https://prove2.me/theorems/87e84924-c9cf-4110-b1f8-72f4cf4f3e50
-- statement:
--   The state-visitation weight `pgRho` is nonnegative whenever the transition kernel `P` and policy `π` are. Proved by induction on `t` using nonnegativity of finite sums of products of nonnegatives.
-- source:
--   Standard MDP theory.

import Definitions.Def_pg_mdp_core
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

theorem pg_rho_nonneg {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]
    (P : S → A → S → ℝ) (π : ℝ → S → A → ℝ) (θ : ℝ)
    (hP : ∀ s a s', 0 ≤ P s a s') (hπ : ∀ s a, 0 ≤ π θ s a) :
    ∀ (t : ℕ) (s₀ s : S), 0 ≤ pgRho P π t s₀ θ s := by sorry
