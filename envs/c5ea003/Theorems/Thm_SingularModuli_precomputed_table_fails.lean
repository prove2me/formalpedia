-- Prove2me | Theorems.Thm_SingularModuli_precomputed_table_fails
-- name    : SingularModuli.precomputed_table_fails
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T21:12:18.210341+00:00
-- url     : https://prove2.me/theorems/9ae0c924-1148-4ab6-8325-69b041c5ac5c
-- title:
--   Precomputation is useless.
-- statement:
--   **Precomputation is useless.** For every fixed table `T` of evaluation points
--   at which `H` does not vanish, and every bound `M`, there are distinct primes
--   `p, q > M` such that every single entry of the table returns `gcd = 1` on the
--   semiprime `N = pq`.  A table computed before seeing `N` therefore cannot factor
--   `N`; the only way to use the structured set is to search it, at the `√N` price
--   of `SqrtBarrier.lean`.
--
--   ```lean
--   theorem SingularModuli.precomputed_table_fails(H : Polynomial ℤ) (T : Finset ℤ) (M : ℕ) :
--       ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ M < p ∧ M < q ∧
--         ∀ t ∈ T, ¬ NontrivialDivisor (p * q) (evalGcd H t (p * q)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/SingularModuli/PrecomputationBarrier.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/SingularModuli/PrecomputationBarrier.lean#L104

-- Thm stub generated from Cryptography/SingularModuli/PrecomputationBarrier.lean
import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_CongruenceOfSquares
import Definitions.Def_Cryptography_SingularModuli_GcdCriterion
import Definitions.Def_Cryptography_SingularModuli_PrecomputationBarrier
import Definitions.Def_Cryptography_SingularModuli_RootCount

/-!
# Singular Moduli Factoring, Step 7: the circularity bottleneck, made a theorem

The useful evaluation points for `H_D` are the roots of `H_D` mod `p` — a set
*defined in terms of the unknown factor* `p`.  The natural way to try to escape
the `√N` search is precomputation: fix once and for all a table `T` of
evaluation points (and a family of discriminants), and hope that some entry of
the table hits a root modulo one of the factors of whatever `N` arrives.

This file proves that this is impossible, in the strongest form:

* `card_catchable_le_sum_log` — a table of `k` evaluation points can ever be
  useful for at most `∑_{t ∈ T} log₂ |H(t)|` primes.  That is a bound depending
  only on the *bit size of the table*, not on `N`;
* `infinite_uncaught_primes` — hence infinitely many primes are invisible to any
  fixed table;
* `precomputed_table_fails` — for every fixed table `T` and every bound `M`
  there are distinct primes `p, q > M` such that **every** entry of the table
  returns `gcd = 1` on `N = pq`: the precomputed attack learns nothing at all;
* `finite_family_table_fails` — the same for a finite family of discriminants
  used simultaneously.

Interpretation: the structured set cannot be enumerated in advance, only
searched, and `SqrtBarrier.lean` prices that search at `√N/(4h)`.  This is the
formal content of "barrier 6" for singular moduli factoring.
-/

open SingularModuli

open Polynomial Finset FactoringBarriers

/-! ## A table catches only logarithmically many primes -/






/-! ## No precomputed table factors anything -/

theorem SingularModuli.precomputed_table_fails(H : Polynomial ℤ) (T : Finset ℤ) (M : ℕ) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ M < p ∧ M < q ∧
      ∀ t ∈ T, ¬ NontrivialDivisor (p * q) (evalGcd H t (p * q)) := by sorry
