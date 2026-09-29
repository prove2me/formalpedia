-- Prove2me | Theorems.Thm_input_valuation_equidistribution_false_v2
-- name    : input_valuation_equidistribution_false_v2
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-29T01:36:56.311056+00:00
-- url     : https://prove2.me/theorems/6875c10e-48e6-4445-af37-fc9811d09bcf
-- title:
--   Valuation-vector equidistribution is false as stated, v2 (self-contained)
-- statement:
--   Disproof node (v2, self-contained statement) for `input_valuation_equidistribution` in the tao-collatz mission: the valuation-vector equidistribution equality is false as published, off by a factor of 2 (counterexample n₀=1, m=1, ā≡1: empty filter, card 0 vs claimed 2^0=1). States the negation for positive-form verification.

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

theorem input_valuation_equidistribution_false_v2 :
    ¬ ∀ n₀ m : ℕ, 1 ≤ n₀ → ∀ ā : Fin n₀ → ℕ, (∀ j, 1 ≤ ā j) →
      Finset.sum Finset.univ (fun j => ā j) ≤ m →
      (Finset.filter (fun r => Odd r ∧ valVec n₀ r = ā) (Finset.range (2 ^ m))).card
        = 2 ^ (m - Finset.sum Finset.univ (fun j => ā j)) := by sorry
