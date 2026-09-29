-- Prove2me | Theorems.Thm_input_syracuse_odd_preserving
-- name    : input_syracuse_odd_preserving
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-29T00:02:39.717027+00:00
-- url     : https://prove2.me/theorems/dd4aeb2d-784c-4777-a583-d67120559de8
-- title:
--   Tao Proposition 1.9 input: the Syracuse map preserves oddness
-- statement:
--   Child decomposition node for `syracuse_first_passage_finite_tail_bound` (b179e2a6-29fd-4151-8b97-35fd2e1bb5a1) in the tao-collatz mission; it is the deepest input used in the Section 5 proof of Tao 2022 Proposition 1.11 estimate (1.19), which is itself the finite-time input to Theorem 3.1. Tao 2022 ('Almost all orbits of the Collatz map attain almost bounded values', Forum of Mathematics, Pi 10 (2022), e12; arXiv:1909.03562v7), section 1.2: the Syracuse map sends odd integers to odd integers — for odd `n`, `Syr(n) = (3n+1)/2^(nu_2(3n+1))` is odd since every factor of 2 is divided out. This parity input is used throughout the Section 5 argument (in particular it guarantees every valuation-vector entry is at least 1, which is what makes the Chernoff mgf product finite).

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

theorem input_syracuse_odd_preserving :
    ∀ n : ℕ, Odd n → Odd (syracuseStep n) := by sorry
