-- Prove2me | Definitions.Def_Bridges_ResidueLeakageCounting
-- name    : Bridges_ResidueLeakageCounting
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:38:43.220961+00:00
-- url     : https://prove2.me/theorems/8178ac58-9096-4527-8a10-6f74e37d8eaa
-- title:
--   Aether Catalog definitions — Bridges_ResidueLeakageCounting
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ResidueLeakageCounting`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ResidueLeakageCounting.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_ResidueLeakagePatternSurjectivity
/-
# Counting the leakage: the fingerprint carries exactly `K` bits

Sixth file of the residue-leakage thread.  `qrFingerprint_range_eq` identifies
the range of the fingerprint on primes with the set of `±1`-vectors of length
`K`.  Here we count that set, so that the leakage curve becomes an exact
number:

`|{ F_A(q) : q prime, q ∉ A }| = 2^K`.

Combined with `dirichlet_no_pruning` this is the quantitative form of the
verdict: the channel emits exactly `K` bits about `N`, and none of them about
the individual factors.
-/


namespace Bridges.ResidueLeakage

/-- The set of `±1`-vectors of length `n`, as lists. -/
def signVectors (n : ℕ) : Set (List ℤ) :=
  {v : List ℤ | v.length = n ∧ ∀ x ∈ v, x = 1 ∨ x = -1}







end Bridges.ResidueLeakage


