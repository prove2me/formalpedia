-- Prove2me | Definitions.Def_Bridges_ResidueLeakagePatternSurjectivity
-- name    : Bridges_ResidueLeakagePatternSurjectivity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:37:59.484863+00:00
-- url     : https://prove2.me/theorems/1db5e506-4509-4cc3-8f77-4a62d93ee3f7
-- title:
--   Aether Catalog definitions — Bridges_ResidueLeakagePatternSurjectivity
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ResidueLeakagePatternSurjectivity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ResidueLeakagePatternSurjectivity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageDirichletNoPruning
/-
# Pattern surjectivity of the QR fingerprint, and the failure of individual pinning

Companion file to `Bridges.ResidueLeakageDirichletNoPruning`.

Where the no-pruning theorem shows that the cheap residue channel cannot *remove*
any candidate prime, this file shows the complementary, constructive fact: the
fingerprint map is **surjective onto all `2^K` sign patterns**, already on primes.
The proof is a genuine cross-domain bridge:

* Chinese remainder theorem (`existsCRT`) to build the residue class,
* quadratic reciprocity + the supplementary law at `2` (`jacobiSym.at_two`),
* existence of a quadratic nonresidue in a finite field
  (`FiniteField.exists_nonsquare`),
* Dirichlet's theorem (imported through `infinite_primes_jacobi_eq`).

Main results:

* `exists_prime_jacobi_pattern` — every prescribed sign pattern on a set of
  distinct odd probe primes, together with a prescribed value at `2`, is
  realised by infinitely many primes.
* `qrFingerprint_pattern_surjective` — the same for an arbitrary list of
  distinct probe primes (the prime `2` allowed): all `2^K` fingerprints occur.
* `no_individual_pinning` — for any observed `F_A(N₀)` and any probe prime `a₀`,
  there are consistent factorisations `p₁q₁` and `p₂q₂` of the *same*
  fingerprint with `(a₀|p₁) = 1` and `(a₀|p₂) = -1`: the data pins down no
  individual symbol of a factor, only the symmetric products.
-/


namespace Bridges.ResidueLeakage

/-! ## A Chinese remainder theorem for lists of moduli -/


/-! ## A quadratic nonresidue witness -/

open Classical in
/-- A natural number that is a quadratic nonresidue mod `p` (for `p` an odd
prime); junk value `0` otherwise. -/
noncomputable def nonresidueWitness (p : ℕ) : ℕ :=
  if h : ∃ r : ℕ, ¬ IsSquare ((r : ZMod p)) then h.choose else 0


/-! ## Building a modulus with a prescribed symbol pattern -/

/-- The residue prescription used in the construction: `1` for a `+1` target,
a quadratic nonresidue for a `-1` target; at the modulus `8` we use
`1` (giving `(2|m) = 1`) or `5` (giving `(2|m) = -1`). -/
noncomputable def patternResidue (e₂ : ℤ) (ε : ℕ → ℤ) (x : ℕ) : ℕ :=
  if x = 8 then (if e₂ = 1 then 1 else 5)
  else if ε x = 1 then 1 else nonresidueWitness x


/-! ## Pattern surjectivity on primes -/



/-! ## No individual pinning -/


/-! ## The exact range of the fingerprint -/



/-! ## Specialisation to the first `K` primes -/




end Bridges.ResidueLeakage


