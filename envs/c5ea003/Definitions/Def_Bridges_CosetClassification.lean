-- Prove2me | Definitions.Def_Bridges_CosetClassification
-- name    : Bridges_CosetClassification
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:24:23.387759+00:00
-- url     : https://prove2.me/theorems/97988efa-a1b1-4ac0-bf84-f9dbf57fce5a
-- title:
--   Aether Catalog definitions — Bridges_CosetClassification
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.CosetClassification`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/CosetClassification.lean by skeleton subtraction
import Mathlib

/-!
# The classification of Donoho–Stark extremals: supports are cosets of subgroups

This file closes *Conjecture 3* of the thread's `FUTURE_DIRECTIONS.md` for every modulus `N`.

`Catalog/Bridges/UncertaintyRigidity.lean` proved modulus rigidity (an extremal is flat on its
support) and `Catalog/Bridges/ExtremalCosets.lean` proved phase rigidity, in the form of the
orthogonality relation `(j - j') * (k - k') = 0` between the difference set of the support and
the difference set of the spectrum. What remains is pure duality bookkeeping: the annihilator of
a subgroup `H ≤ ZMod N` has exactly `N / |H|` elements. Combining the two, the difference set of
the support is squeezed between a subgroup and a set of the same cardinality, hence *is* that
subgroup, so the support is a coset.

## Main results

* `CosetClassification.card_annihilator_mul_card` : `|ann H| * |H| = N` for every additive
  subgroup `H` of `ZMod N`, proved by a double character sum.
* `CosetClassification.extremal_support_coset` : **the classification.** If `Φ ≠ 0` attains
  `|supp Φ| * |supp 𝓕Φ| = N`, then `supp Φ` is a coset `a + K` of a subgroup `K ≤ ZMod N` with
  `|K| = |supp Φ|`; dually `supp 𝓕Φ` is a coset of the annihilator of `K`.
* `CosetClassification.extremal_eq_modulated_coset_indicator` : combined with flatness and phase
  rigidity, an extremal is a constant multiple of a character times the indicator of a coset.
* `CosetClassification.card_support_dvd_of_extremal` : in particular the support size of an
  extremal divides `N`, and `CosetClassification.extremal_additive_divisor_sum` : its additive
  support sum is the divisor sum `d + N / d` — both testable numeric consequences.
-/

open Finset ZMod

namespace CosetClassification

variable {N : ℕ} [NeZero N]

/-! ## 1. Annihilators and their cardinality -/

open scoped Classical in
/-- The annihilator of a finite subset of `ZMod N`. -/
noncomputable def annFinset (A : Finset (ZMod N)) : Finset (ZMod N) :=
  Finset.univ.filter fun x => ∀ a ∈ A, a * x = 0








/-! ## 2. The classification of extremals -/







end CosetClassification


