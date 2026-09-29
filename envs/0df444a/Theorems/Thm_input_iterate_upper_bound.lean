-- Prove2me | Theorems.Thm_input_iterate_upper_bound
-- name    : input_iterate_upper_bound
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-29T00:02:56.114837+00:00
-- url     : https://prove2.me/theorems/dfc33116-034f-491f-8b10-470c229f77e0
-- title:
--   Tao 2022, (1.7) plus (1.13): Syracuse iterate upper bound
-- statement:
--   Child decomposition node for `syracuse_first_passage_finite_tail_bound` (b179e2a6-29fd-4151-8b97-35fd2e1bb5a1) in the tao-collatz mission; it is the deepest input used in the Section 5 proof of Tao 2022 Proposition 1.11 estimate (1.19), which is itself the finite-time input to Theorem 3.1. Tao 2022, (1.7) + (1.13): the Syracuse iterate upper bound. From (1.7), `Syr^n(N) = 3^n 2^{-|a|} N + F_n(a)`, and (1.13) gives `0 <= F_n(a) <= 3^n`, whence the bound. This is the passage-time input: combined with the high-valuation event, it is what forces the `n_0`-th Syracuse iterate of a window element below `x`, so that the no-first-passage event sits inside the low-valuation (bad) event.

import Mathlib
import Definitions.Def_syracuseOrbitMin

noncomputable section


attribute [instance] Classical.propDecidable

/-- The 2-adic valuation of `3n+1` (Tao 2022, section 1.2). -/
def syrVal (n : ℕ) : ℕ := Nat.factorization (3 * n + 1) 2

/-- The Syracuse valuation vector of length `n₀` (Tao 2022, (1.8)). -/
def valVec (n₀ : ℕ) (n : ℕ) : Fin n₀ → ℕ := fun j => syrVal (syracuseStep^[j.val] n)

/-- The valuation-vector sum (Tao 2022, (1.4)). -/
def valSum (n₀ n : ℕ) : ℕ := Finset.sum Finset.univ (fun j => valVec n₀ n j)

theorem input_iterate_upper_bound :
    ∀ n₀ n : ℕ, Odd n →
      ((syracuseStep^[n₀] n : ℕ) : ℝ)
        ≤ (3 : ℝ) ^ n₀ * n / (2 : ℝ) ^ (valSum n₀ n) + (3 : ℝ) ^ n₀ := by sorry
