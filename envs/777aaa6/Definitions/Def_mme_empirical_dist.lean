-- Prove2me | Definitions.Def_mme_empirical_dist
-- name    : mme_empirical_dist
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-06-05T03:32:54.762313+00:00
-- url     : https://prove2.me/theorems/4c37e1e9-60e8-4514-a02c-0e27fd99920d
-- statement:
--   The empirical distribution (symbol-count profile) of a finite string $\tau:\mathrm{Fin}\,N\to\alpha$.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
open BigOperators
universe u

/-- The empirical distribution of a string `τ : Fin N → α`: for each symbol `σ`, the count of positions carrying it. -/
noncomputable def empiricalDist {α : Type u} [DecidableEq α] {N : ℕ}
    (τ : Fin N → α) : α → ℕ :=
  fun σ => (Finset.univ.filter (fun k : Fin N => τ k = σ)).card


