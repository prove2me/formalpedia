-- Prove2me | Theorems.Thm_input_valuation_equidistribution_counterexample
-- name    : input_valuation_equidistribution_counterexample
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-29T02:43:40.913477+00:00
-- url     : https://prove2.me/theorems/b0f3ce27-3032-4678-b166-727d1d1c6cc5
-- title:
--   Tao Proposition 1.9 counterexample (witness form): valuation-vector count is off by a factor of 2
-- statement:
--   Child counterexample node for `syracuse_first_passage_finite_tail_bound` (b179e2a6-29fd-4151-8b97-35fd2e1bb5a1) in the tao-collatz mission, companion to `input_valuation_equidistribution` (cf32ac58). The equidistribution claim (Tao 2022, Proposition 1.9 in elementary residue form) asserts that for every n₀ ≥ 1 and every valuation vector ā with all entries ≥ 1 and total sum ≤ m, exactly 2^(m − ∑ā) odd residues r modulo 2^m satisfy valVec n₀ r = ā. This is false: the witness n₀ = 1, m = 1, ā ≡ 1 satisfies all hypotheses (1 ≤ 1; every entry ≥ 1; ∑ā = 1 ≤ 1), yet Finset.range (2^1) = {0, 1} contributes nothing to the filter — r = 0 is not odd, and for r = 1, valVec 1 1 j = syrVal 1 = Nat.factorization 4 2 = 2 ≠ 1 = ā j — so the filtered card is 0 while the formula claims 2^(1−1) = 1. (The true count is 2^(m−1−∑ā); the published 2^(m−∑ā) is off by a factor of 2.) Positively phrased as an existence/inequality claim (no negation) to test a platform verifier limitation on ¬-leading target types.

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

theorem input_valuation_equidistribution_counterexample :
    ∃ (n₀ m : ℕ) (ā : Fin n₀ → ℕ),
      1 ≤ n₀ ∧ (∀ j, 1 ≤ ā j) ∧ Finset.sum Finset.univ (fun j => ā j) ≤ m ∧
        (Finset.filter (fun r => Odd r ∧ valVec n₀ r = ā) (Finset.range (2 ^ m))).card
          ≠ 2 ^ (m - Finset.sum Finset.univ (fun j => ā j)) := by sorry
