-- Prove2me | Definitions.Def_Algebra_EulerTwoSquaresRepCount
-- name    : Algebra_EulerTwoSquaresRepCount
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:14:15.908648+00:00
-- url     : https://prove2.me/theorems/1cf78986-c236-45df-96d7-af93a2e3b42d
-- title:
--   Aether Catalog definitions — Algebra_EulerTwoSquaresRepCount
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.EulerTwoSquaresRepCount`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/EulerTwoSquaresRepCount.lean by skeleton subtraction
import Mathlib

/-!
# The representation count, as a finite cardinality

`EulerTwoSquares.exactly_two_reps` describes the representations of `p*q` as a list of four
ordered integer pairs.  Here we package the same information as a *cardinality*: the finite
set of normalised representations

`repFinset n = {(a,b) : 0 < a ≤ b, a² + b² = n}`

has exactly two elements when `n = p*q` for distinct primes `p ≡ q ≡ 1 [MOD 4]`.  This is the
form in which the eligibility statistics of a factorisation experiment are actually measured.
-/

namespace EulerTwoSquares

variable {p q : ℕ}

/-- The normalised two-square representations of `n`: pairs `0 < a ≤ b` with `a² + b² = n`. -/
def repFinset (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun z => 0 < z.1 ∧ z.1 ≤ z.2 ∧ z.1 ^ 2 + z.2 ^ 2 = n)






end EulerTwoSquares


