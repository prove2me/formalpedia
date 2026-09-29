-- Prove2me | Theorems.Thm_input_valuation_factors
-- name    : input_valuation_factors
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-29T00:02:56.384281+00:00
-- url     : https://prove2.me/theorems/5113665b-d375-4c17-9c96-e9fc5e28620c
-- title:
--   Tao Proposition 1.9 factoring clause: valuation vector determined by residue class
-- statement:
--   Child decomposition node for `syracuse_first_passage_finite_tail_bound` (b179e2a6-29fd-4151-8b97-35fd2e1bb5a1) in the tao-collatz mission; it is the deepest input used in the Section 5 proof of Tao 2022 Proposition 1.11 estimate (1.19), which is itself the finite-time input to Theorem 3.1. Factoring clause of Tao 2022, Proposition 1.9: if the valuation sum of an odd `n` is at most `m`, the valuation vector `a^(n_0)(n)` is already determined by `n mod 2^m`. The valuations only inspect the lowest `sum a <= m` bits of `n` (same bit-pinning induction as the equidistribution clause). This is the input that lets the window-counting argument inject each bad window element into a residue class times a quotient range.

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

theorem input_valuation_factors :
    ∀ n₀ n m : ℕ, Odd n → valSum n₀ n ≤ m →
      valVec n₀ n = valVec n₀ (n % 2 ^ m) := by sorry
