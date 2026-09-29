-- Prove2me | Theorems.Thm_input_valuation_factors_false
-- name    : input_valuation_factors_false
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-29T01:45:42.541953+00:00
-- url     : https://prove2.me/theorems/a2fe970c-5365-4531-a4e8-02fdad93d41d
-- title:
--   Tao Proposition 1.9 factoring clause is false as stated (residue loses the top bit)
-- statement:
--   Disproof node for `input_valuation_factors` (5113665b-d375-4c17-9c96-e9fc5e28620c) in the tao-collatz mission: the stated factoring clause is false as published. Counterexample: n₀=1, n=3, m=1 satisfies Odd 3 and valSum 1 3 = ν₂(10) = 1 ≤ 1, but valVec 1 3 ≠ valVec 1 (3 % 2^1): at j=⟨0,⟩ the LHS is syrVal 3 = 1 while the RHS is syrVal 1 = ν₂(4) = 2. The claim needs the residue to retain the low ν₂(3n+1)+1 bits; n % 2^m keeps only m bits. This node states the negation so the disproof can be checked in positive form (the platform auto-rejects ¬-form submissions against the original node).

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

theorem input_valuation_factors_false :
    ¬ ∀ n₀ n m : ℕ, Odd n → valSum n₀ n ≤ m →
      valVec n₀ n = valVec n₀ (n % 2 ^ m) := by sorry
