-- Prove2me | Theorems.Thm_input_valuation_equidistribution_false
-- name    : input_valuation_equidistribution_false
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-29T01:14:41.500291+00:00
-- url     : https://prove2.me/theorems/c017dfd8-5fea-403b-b073-b63e0342f8c1
-- title:
--   Valuation-vector equidistribution is false as stated (off by a factor of 2)
-- statement:
--   Disproof node for `input_valuation_equidistribution` (cf32ac58-dc23-436e-874f-578f99027eea) in the tao-collatz mission: the stated valuation-vector equidistribution equality is false as published — it is off by a factor of 2. Counterexample: n₀=1, m=1, ā≡1 gives an empty filtered finset (card 0) while the claimed right-hand side is 2^(1-1)=1 (valVec 1 1 = syrVal 1 = 2 ≠ 1). The true residue count is 2^(m-1-∑ā). This node states the negation so the disproof can be checked in positive form (the platform auto-rejects ¬-form submissions against the original node).

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

theorem input_valuation_equidistribution_false :
    ¬ ∀ n₀ m : ℕ, 1 ≤ n₀ → ∀ ā : Fin n₀ → ℕ, (∀ j, 1 ≤ ā j) →
      Finset.sum Finset.univ (fun j => ā j) ≤ m →
      (Finset.filter (fun r => Odd r ∧ valVec n₀ r = ā) (Finset.range (2 ^ m))).card
        = 2 ^ (m - Finset.sum Finset.univ (fun j => ā j)) := by sorry
