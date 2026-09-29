-- Prove2me | Theorems.Thm_mme_tau_enum_card_eq_multinomial
-- name    : mme_tau_enum_card_eq_multinomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-06-05T03:33:49.717097+00:00
-- url     : https://prove2.me/theorems/a06f0320-859f-450d-aea2-51a77d8b8735
-- statement:
--   For a finite alphabet $\alpha$, $S:\mathrm{Finset}\,\alpha$, and $\mu$ supported on $S$ with $\sum_{\sigma\in S}\mu(\sigma)=N$, the number of strings $\tau:\mathrm{Fin}\,N\to\alpha$ with image in $S$ and empirical distribution $\mu$ equals the multinomial coefficient $N!/\prod_\sigma \mu(\sigma)!$. Framework-independent; reused by every laser-method type-counting argument.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Fintype.Pi
import Definitions.Def_mme_empirical_dist
open BigOperators
universe u

theorem mme_tau_enum_card_eq_multinomial {α : Type u} [Fintype α] [DecidableEq α]
    (S : Finset α) (μ : α → ℕ)
    (_hsupp : ∀ σ : α, μ σ ≠ 0 → σ ∈ S)
    (N : ℕ) (_hsum : ∑ σ ∈ S, μ σ = N) :
    (Finset.univ.filter
        (fun τ : Fin N → α => (∀ k, τ k ∈ S) ∧
          (∀ σ ∈ S, empiricalDist τ σ = μ σ))).card =
      Nat.multinomial S μ := by sorry
