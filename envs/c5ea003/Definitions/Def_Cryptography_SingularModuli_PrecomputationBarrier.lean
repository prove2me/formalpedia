-- Prove2me | Definitions.Def_Cryptography_SingularModuli_PrecomputationBarrier
-- name    : Cryptography_SingularModuli_PrecomputationBarrier
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:35:28.086677+00:00
-- url     : https://prove2.me/theorems/d2ea2e31-7ee8-4a2e-8497-b7f33671bad5
-- title:
--   Aether Catalog definitions — Cryptography_SingularModuli_PrecomputationBarrier
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.SingularModuli.PrecomputationBarrier`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/SingularModuli/PrecomputationBarrier.lean by skeleton subtraction
import Mathlib
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

namespace SingularModuli

open Polynomial Finset FactoringBarriers

/-! ## A table catches only logarithmically many primes -/


/-- The set of primes that a fixed table `T` of evaluation points can ever
detect, for the polynomial `H`: the primes dividing one of the values `H(t)`. -/
noncomputable def catchable (H : Polynomial ℤ) (T : Finset ℤ) : Finset ℕ :=
  T.biUnion (fun t => (H.eval t).natAbs.primeFactors)




/-! ## No precomputed table factors anything -/






end SingularModuli


