-- Prove2me | Definitions.Def_Applications_GcdRevealBarrier
-- name    : Applications_GcdRevealBarrier
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:46:36.323724+00:00
-- url     : https://prove2.me/theorems/407c1c04-e085-444b-8899-ae27d6e22d7e
-- title:
--   Aether Catalog definitions — Applications_GcdRevealBarrier
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.GcdRevealBarrier`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/GcdRevealBarrier.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_ThreeSumFactoring
/-
# A universal information-theoretic barrier for gcd-based factor reveals

Third cycle of the 3SUM / birthday-bound investigation.

Cycles 1–2 (`Catalog/Applications/ThreeSumFactoring.lean`,
`Catalog/Applications/BirthdayBoundHierarchy.lean`,
`Catalog/Applications/ThreeSumSearchSpace.lean`) proved a `√N` barrier for two
*specific* mechanisms: the pigeonhole cost of a level-`r` collision and the
magnitude of the entries needed for a witness to exist at all.  The obvious
objection is that a cleverer collision rule might escape both.  This file removes
that escape route for the entire class of methods that the hierarchy belongs to.

**The abstraction.**  Every method in the hierarchy — sumset collisions, 3SUM
collisions, singular-moduli evaluations, Pollard rho, `p−1` — produces a finite
list `V` of integers and tests `gcd(v, N)` for `v ∈ V`.  Such a method *reveals*
a prime `p` exactly when `p ∣ v` for some `v ∈ V`.  Nothing else about the
method matters.

**The theorem.**  A value `v ≤ B` has at most `log₂ B` distinct prime factors,
so a value list of length `W` can reveal at most `W · log₂ B` primes
(`card_revealedPrimes_le`).  Hence a method whose value list is *universal* for
the primes below `M` must satisfy

  `π(M) ≤ W · log₂ B`   (`universal_work_lower_bound`).

For balanced semiprimes one must take `M ≈ √N`, so with values of polynomial
size `B = N ^ O(1)` the work is `W = Ω(π(√N) / log N)`: a `√N`-type barrier for
*every* gcd-based reveal method, uniform in the collision structure.  The three
rows of the hierarchy table are then instances of a single obstruction rather
than a coincidence.
-/

namespace GcdRevealBarrier

open Finset

/-! ## Value lists and the primes they reveal -/

/-- The primes revealed by a value list `V`: those dividing some tested value. -/
def revealedPrimes (V : Finset ℕ) : Finset ℕ := V.biUnion Nat.primeFactors




/-! ## The universal lower bound -/

/-- A value list is *universal below `M`* when every prime `p < M` divides one of
its entries; this is exactly the property "the method factors every semiprime
whose smaller prime factor is below `M`". -/
def UniversalBelow (V : Finset ℕ) (M : ℕ) : Prop :=
  ∀ p, p.Prime → p < M → ∃ v ∈ V, p ∣ v




/-! ## Instantiation: the collision hierarchy obeys the universal bound -/



end GcdRevealBarrier


