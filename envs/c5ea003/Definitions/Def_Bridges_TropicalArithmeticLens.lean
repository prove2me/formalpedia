-- Prove2me | Definitions.Def_Bridges_TropicalArithmeticLens
-- name    : Bridges_TropicalArithmeticLens
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:28:02.644067+00:00
-- url     : https://prove2.me/theorems/5468386c-c0b0-4086-928a-45e8515bc12b
-- title:
--   Aether Catalog definitions — Bridges_TropicalArithmeticLens
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalArithmeticLens`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalArithmeticLens.lean by skeleton subtraction
import Mathlib

/-!
# Tropical Arithmetic Lensing on the Berggren Tree

## Overview

This module develops a novel formal bridge between three mathematical worlds:
1. **The Berggren tree** of primitive Pythagorean triples
2. **Tropical (min-plus) path actions** on weighted arithmetic trees
3. **Arithmetic reconstruction** of prime factorization signatures from caustic profiles

## Central Discovery

Factorization information can be encoded as a tropical optical profile on the
Berggren tree and then rigidly recovered from its caustics. Specifically:

- The **prime interaction profile** of a number n records which primes appear as
  common factors of n and hypotenuses of Berggren-tree triples.
- **Caustic rigidity**: equal profiles over a sufficient probe set force equal
  prime factor supports.
- A **certified reconstruction algorithm** extracts prime factor candidates from
  the profile with a formal soundness guarantee.

## Main Results

### Berggren Tree Structure
- `childA_preserves_pythag`, `childB_preserves_pythag`, `childC_preserves_pythag`:
  Berggren child maps preserve the Pythagorean property.
- `childA_hyp_increase`, `childB_hyp_increase`, `childC_hyp_increase`:
  All child maps strictly increase the hypotenuse for positive triples.

### Tropical Path Actions
- `tropicalLensAction_append`: Tropical action is additive on path concatenation.
- `tropicalLensAction_mono`: Pointwise height domination implies action domination.
- `tropicalLensAction_map_mono`: Child maps that increase height yield larger actions.

### Caustic Profiles and Rigidity
- `causticHeightProfile_mono`: Profile monotonicity under height domination.
- `interaction_profile_eq_of_sufficient`: The prime interaction profile equals the
  full prime factor set when the probe set is sufficient.
- `caustic_rigidity`: Equal profiles over sufficient probes imply equal prime supports.
- `caustic_rigidity_squarefree`: Specialization to squarefree integers.

### Certified Reconstruction
- `reconstructCandidates_sound`: All prime factors appear in extracted candidates.
- `reconstructCandidates_exact`: Exactness when probes are sufficient.
- `reconstructCandidates_bounded`: The candidate set is always bounded.
-/

open Finset Nat List

namespace TropicalArithmeticLens

/-! ## §1. Berggren Tree Infrastructure

The Berggren tree organizes all primitive Pythagorean triples as a ternary tree
rooted at (3, 4, 5). The three child maps A, B, C are integer-linear
transformations that preserve the Pythagorean property a² + b² = c².

These definitions mirror the catalog (`BerggrenPythagoreanCore`) but are
self-contained here for modularity.
-/

/-- A triple (a, b, c) over ℤ is Pythagorean when a² + b² = c². -/
def IsPythag (a b c : ℤ) : Prop := a ^ 2 + b ^ 2 = c ^ 2

/-- Berggren child map A: (a,b,c) ↦ (a−2b+2c, 2a−b+2c, 2a−2b+3c). -/
def childA (a b c : ℤ) : ℤ × ℤ × ℤ :=
  (a - 2 * b + 2 * c, 2 * a - b + 2 * c, 2 * a - 2 * b + 3 * c)

/-- Berggren child map B: (a,b,c) ↦ (a+2b+2c, 2a+b+2c, 2a+2b+3c). -/
def childB (a b c : ℤ) : ℤ × ℤ × ℤ :=
  (a + 2 * b + 2 * c, 2 * a + b + 2 * c, 2 * a + 2 * b + 3 * c)

/-- Berggren child map C: (a,b,c) ↦ (−a+2b+2c, −2a+b+2c, −2a+2b+3c). -/
def childC (a b c : ℤ) : ℤ × ℤ × ℤ :=
  (-a + 2 * b + 2 * c, -2 * a + b + 2 * c, -2 * a + 2 * b + 3 * c)




/-! ## §2. Hypotenuse Growth Under Berggren Child Maps

Every Berggren child map strictly increases the hypotenuse c when applied to a
positive Pythagorean triple. This is the fundamental geometric fact underlying
the monotonicity of tropical lens actions.

For positive (a,b,c) with a²+b²=c²:
- c > a and c > b (hypotenuse is largest side)
- childA hypotenuse = 2a − 2b + 3c = c + 2(a − b + c) > c since a + c > b
- childB hypotenuse = 2a + 2b + 3c > 3c > c
- childC hypotenuse = −2a + 2b + 3c = c + 2(b − a + c) > c since b + c > a
-/

/-
Child A strictly increases the hypotenuse for positive Pythagorean triples.
-/

/-
Child B strictly increases the hypotenuse (immediate from positivity).
-/

/-
Child C strictly increases the hypotenuse for positive Pythagorean triples.
-/

/-! ## §3. Tropical Path Action

The tropical lens action is the sum of height potentials along a path in
the Berggren tree. In the min-plus semiring, this corresponds to the cost
of a tropical geodesic.
-/



/-- Tropical lens action: sum of a height function along a path.
    In tropical geometry, this is the total cost of a min-plus geodesic. -/
def tropicalLensAction {α : Type*} (H : α → ℕ) (path : List α) : ℕ :=
  (path.map H).sum



/-
Tropical action is additive on path concatenation:
    the action of a composed path equals the sum of the actions.
-/

/-
**Monotonicity under height domination**: if H₁ ≤ H₂ pointwise,
    then the tropical action under H₁ is ≤ the action under H₂.
    This is the tropical analogue of gravitational lens monotonicity:
    a denser mass distribution produces larger deflection angles.
-/

/-
**Functoriality under child maps**: if f increases height,
    then the tropical action of a mapped path dominates the original.
    For Berggren child maps (which increase hypotenuse), this gives
    monotonicity of tropical actions under tree descent.
-/


/-! ## §4. Caustic Height Profiles

The caustic profile records the image of a height function over a finite set
of Berggren nodes. Profile monotonicity is the key structural property
enabling arithmetic comparison through tropical lensing.
-/

/-- The caustic height profile: the set of height values attained by
    elements of a finite probe set S. -/
def causticHeightProfile {α : Type*} (H : α → ℕ) [DecidableEq ℕ] (S : Finset α) : Finset ℕ :=
  S.image H

/-- A partial order on profiles: P₁ ≤ P₂ if every value in P₁ is
    dominated by some value in P₂. This captures the tropical order
    on min-plus envelopes. -/
def profileLe (P₁ P₂ : Finset ℕ) : Prop :=
  ∀ x ∈ P₁, ∃ y ∈ P₂, x ≤ y

/-
Profile order is reflexive.
-/

/-
**Profile monotonicity**: pointwise height domination implies
    profile domination. If one height function is everywhere ≤ another,
    then the corresponding caustic profiles respect the profile order.
    This is the optical comparison principle for tropical lenses.
-/

/-! ## §5. Prime Interaction Profiles and Caustic Rigidity

The prime interaction profile of a natural number n with respect to a probe set S
records all primes that appear as common factors of n and elements of S. This is
the arithmetic content extracted from the tropical lens.

**Central insight**: the probe set S consists of hypotenuses (or products abc) of
Berggren-tree triples. The tropical lens action determines which triples contribute
to the profile and at what cost. Rigidity says: equal profiles over sufficient
probes force equal prime supports.
-/

/-- The prime interaction profile: the set of primes that divide both n
    and some element of the probe set S. This is the "arithmetic caustic"
    that records factorization information visible through the tropical lens. -/
def primeInteractionProfile (n : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.biUnion (fun s => (Nat.gcd n s).primeFactors)

/-- The prime support signature: the set of prime factors of n.
    This is the target of arithmetic reconstruction. -/
def primeSupportSignature (n : ℕ) : Finset ℕ := n.primeFactors

/-- A probe set S is sufficient for n if every prime factor of n divides
    some element of S. Intuitively, the tropical lens "sees" all primes in n.
    In the Berggren tree context, this means every prime dividing n also
    divides some hypotenuse at the given depth. -/
def IsSufficientProbeSet (n : ℕ) (S : Finset ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, ∃ s ∈ S, p ∣ s

/-
Key lemma: a prime factor of n that divides some probe element appears
    in the prime interaction profile. This is the "visibility" property:
    if the lens can see a prime, it records it.
-/

/-
Every element of the prime interaction profile divides n.
    This is the "faithfulness" property: the lens does not hallucinate primes.
    Requires all probe elements to be nonzero.
-/

/-
If S is sufficient for n, the prime interaction profile equals n's
    full prime factor set. Combines visibility and faithfulness.
-/

/-
**Caustic Rigidity Theorem**: if two nonzero numbers have the same prime
    interaction profile over a probe set that is sufficient for both, then
    they have the same prime factor support.

    This is the central theorem of tropical arithmetic lensing: factorization
    data is rigidly determined by the tropical caustic profile on the
    Berggren tree.

    Proof idea: By `interaction_profile_eq_of_sufficient`, the profile of n
    equals n.primeFactors and similarly for m. Profile equality then gives
    n.primeFactors = m.primeFactors.
-/

/-
**Squarefree caustic rigidity**: specialization of the rigidity theorem
    to the squarefree regime. In this case, the prime support completely
    determines the radical of the number.
-/

/-! ## §6. Certified Reconstruction Algorithm

The reconstruction algorithm extracts candidate prime factors from a prime
interaction profile. The profile elements are already primes (since they come
from primeFactors of gcd values), so reconstruction is essentially a filter.

This gives a certified inverse algorithm: from tropical caustic data on the
Berggren tree, we can extract a finite candidate set that provably contains
all true prime factors.
-/

/-- Extract candidate prime factors from a profile.
    Since profile elements come from `primeFactors` of gcd values,
    they are already prime; we filter for primality as a soundness check. -/
def reconstructCandidates (prof : Finset ℕ) : Finset ℕ :=
  prof.filter Nat.Prime

/-
**Reconstruction soundness**: all prime factors of n appear in the
    candidates extracted from n's prime interaction profile, provided
    the probe set is sufficient.

    This is the soundness guarantee of the certified inverse algorithm:
    no true prime factor is missed.
-/

/-
**Candidate boundedness**: the candidate set is finite and bounded.
    Since Finset is inherently finite, we get an explicit upper bound.
-/

/-
**Reconstruction exactness**: when the probe set is sufficient,
    reconstruction gives exactly the prime support signature.

    This is the exactness guarantee: no spurious primes are introduced.
-/

/-! ## §7. Concrete Berggren Tree Computations

Verification that the (3,4,5) root and its first-generation children
satisfy the Pythagorean property and exhibit hypotenuse growth.
-/






end TropicalArithmeticLens


