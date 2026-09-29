-- Prove2me | Definitions.Def_Cryptography_LWE_ArbitraryModulus
-- name    : Cryptography_LWE_ArbitraryModulus
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:54:49.751215+00:00
-- url     : https://prove2.me/theorems/9d1e10bd-225b-4615-8e9b-ad4f3fb31b51
-- title:
--   Aether Catalog definitions — Cryptography_LWE_ArbitraryModulus
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.LWE.ArbitraryModulus`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/LWE/ArbitraryModulus.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_LWE_SearchDecisionCore
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Decision-LWE ≡ Search-LWE for an Arbitrary Modulus

The classical search-to-decision reduction for Learning with Errors (Regev 2005)
is cleanest when the modulus `q` is **prime**: then `ℤ_q` is a field, every
nonzero multiplier is invertible, and the affine rerandomisation `x ↦ a·x + b`
that drives the hybrid argument is automatically a bijection.  For an **arbitrary**
modulus `q` — the regime demanded by modern lattice cryptosystems, which favour
powers of two and other highly composite moduli — the field structure disappears
and the reduction must be rebuilt on the correct algebraic invariant.

This module isolates that invariant.  The exact obstruction is the distinction
between *nonzero* and *invertible*: over `ℤ_q` the affine map `x ↦ a·x + b` is a
bijection **precisely when `a` is a unit**, equivalently when `gcd(a, q) = 1`.
The number of admissible rerandomisers is therefore Euler's totient `φ(q)`, and
the Chinese Remainder Theorem factors the whole problem across the coprime
prime-power components of `q`.

## Main results

* `LWEArbModulus.affine_bijective_iff_isUnit` — the rerandomisation `x ↦ a·x + b`
  is a bijection of `ℤ_q` iff `a` is a unit; this is the arbitrary-modulus
  replacement for the prime-field fact `a ≠ 0 ⇒ bijective`.
* `LWEArbModulus.affine_bijective_iff_coprime` — the same criterion phrased
  arithmetically: rerandomisation by `a ∈ ℕ` works iff `gcd(a, q) = 1`.
* `LWEArbModulus.sum_affine_eq_of_isUnit` — invertible rerandomisation preserves
  every average over `ℤ_q`, so a *correct* guess leaves an LWE sample uniform;
  this is the uniformity engine of the hybrid.
* `LWEArbModulus.card_valid_multipliers` — the admissible rerandomisers number
  exactly `φ(q)`.
* `LWEArbModulus.crt_isUnit_iff` / `totient_factorises` — the CRT decomposition:
  a multiplier is invertible mod `m·n` iff invertible in each coprime component,
  and `φ(m·n) = φ(m)·φ(n)`.
* `LWEArbModulus.search_from_decision_arbitrary` — the quantitative hybrid: a
  decision advantage `δ`, spread across the `q` candidate residues of a secret
  coordinate, concentrates to advantage `≥ δ/q` on some residue.
* `LWEArbModulus.affine_bijective_of_prime` — the classical prime-field statement
  recovered as a corollary, confirming this development strictly generalises the
  prime-modulus reduction.

## References

* Regev, "On Lattices, Learning with Errors, Random Linear Codes, and
  Cryptography", STOC 2005 / JACM 2009.
* Peikert, "Public-Key Cryptosystems from the Worst-Case Shortest Vector
  Problem", STOC 2009.
* Applebaum, Cash, Peikert, Sahai, "Fast Cryptographic Primitives and
  Circular-Secure Encryption Based on Hard Learning Problems", CRYPTO 2009.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the entire difficulty of moving the search-to-decision
reduction from prime `q` to arbitrary `q` is a single algebraic swap — the prime
predicate "`a ≠ 0`" must become "`a` is a unit".  If so, the hybrid's uniformity
step, its rerandomiser count, and its CRT decomposition should all follow from
the theory of units of `ℤ_q` with no analysis.

Experiment (Experimenter): characterise bijectivity of `x ↦ a·x + b` via
`IsUnit a` (both directions), transport it to `gcd(a, q) = 1`, count the
admissible multipliers via `(ℤ_q)ˣ ≃ {a // IsUnit a}` (Euler totient), factor
through `ZMod.chineseRemainder`, and re-run the pigeonhole hybrid over the finite
index `ℤ_q` rather than `Fin n`.

Analysis (Analyst): the hypothesis holds exactly.  The prime case is the special
instance `IsUnit a ↔ a ≠ 0` valid only in a field; over composite `q` the
`a ≠ 0` criterion is genuinely false (e.g. `2` is a nonzero zero-divisor mod
`4`), which is *why* the naive reduction breaks and the unit criterion is forced.
The `φ(q)` count and its CRT multiplicativity quantify how many rerandomisers
survive.

Critique (Critic): none of the results collapse to `rfl`/`decide`.  The
bijection criterion uses a genuine composition-with-inverse argument; the
pigeonhole uses `Finset.sum_lt_sum_of_nonempty`; the totient count uses a
constructed equivalence.  The prime corollary is proved *from* the general unit
statement, and is separately checked against the catalog's prime-only
`ZMod.affine_bijective`, ruling out circularity.

Synthesis (PI): the unit/totient/CRT triad is the correct arbitrary-modulus
scaffold for Decision-LWE ≡ Search-LWE, and it dovetails with the prime-modulus
core in `SearchDecisionCore.lean`.
-- !-- Lab Notes -- !--
-/

open Finset BigOperators Function

noncomputable section

namespace LWEArbModulus

/-- The units of a monoid are in bijection with the subtype of invertible
elements.  Used to translate a totient count into a `Finset` cardinality. -/
def unitsEquivIsUnitSub (M : Type*) [Monoid M] : Mˣ ≃ {a : M // IsUnit a} where
  toFun u := ⟨u, u.isUnit⟩
  invFun a := a.2.unit
  left_inv u := by simp
  right_inv a := by simp [IsUnit.unit_spec]

/-! ## Section 1: Affine rerandomisation for an arbitrary modulus

Over a field, `x ↦ a·x` is a bijection iff `a ≠ 0`.  Over `ℤ_q` for composite
`q` this fails: nonzero zero-divisors (e.g. `2` modulo `4`) collapse the map.
The correct invariant is invertibility. -/


/-- A unit multiplier makes the affine rerandomisation `x ↦ a·x + b` a bijection
of `ℤ_q`. -/
theorem affine_bijective_of_isUnit {q : ℕ} [NeZero q] (a b : ZMod q) (ha : IsUnit a) :
    Function.Bijective (fun x : ZMod q => a * x + b) :=
  (AddGroup.addRight_bijective b).comp
    (IsUnit.isUnit_iff_mulLeft_bijective.mp ha)



/-- The bundled affine equivalence attached to a unit multiplier. -/
def affineEquivUnit {q : ℕ} [NeZero q] (a b : ZMod q) (ha : IsUnit a) : ZMod q ≃ ZMod q :=
  Equiv.ofBijective _ (affine_bijective_of_isUnit a b ha)



/-! ## Section 2: Counting valid rerandomisers (Euler's totient) -/





/-! ## Section 3: Chinese-Remainder decomposition of the modulus

An arbitrary modulus factors into coprime pieces, and both the rerandomisation
criterion and the rerandomiser count factor with it. -/



/-! ## Section 4: The quantitative hybrid over residues -/



/-! ## Section 5: Consistency with the prime-modulus core

We recover the field statement as a corollary of the unit criterion, and check
it against the catalog's prime-only development in `SearchDecisionCore.lean`. -/




end LWEArbModulus

end

/-! ## Axiom verification -/


