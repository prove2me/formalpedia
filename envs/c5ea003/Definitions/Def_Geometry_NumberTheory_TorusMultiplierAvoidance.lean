-- Prove2me | Definitions.Def_Geometry_NumberTheory_TorusMultiplierAvoidance
-- name    : Geometry_NumberTheory_TorusMultiplierAvoidance
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:45:31.203792+00:00
-- url     : https://prove2.me/theorems/b6980ea1-bc83-4085-93b3-b61d7345e933
-- title:
--   Aether Catalog definitions — Geometry_NumberTheory_TorusMultiplierAvoidance
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.NumberTheory.TorusMultiplierAvoidance`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/NumberTheory/TorusMultiplierAvoidance.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A finite-torus multiplier avoidance theorem

For a prime `p`, work over the finite field `F = ZMod p` and the finite torus
`F × F`.  Given a set `D` of nonzero displacement vectors with `D.card < p`, we
produce a single multiplier `a : F × F` that "avoids" every displacement, in the
sense that the dot product `d.1 * a.1 + d.2 * a.2` is nonzero for all `d ∈ D`.

The proof is a clean finite-cardinality counting argument (replacing earlier
circular/infinite lacunary reasoning):

* For each nonzero `d`, the "bad" set of multipliers killing `d` is a line in the
  torus, so it has at most `p` points (`bad_card_le`).
* The union of the `D.card` bad lines has fewer than `p * p` points, while the
  whole torus has exactly `p * p` points.  Hence some multiplier escapes every
  bad line.

## Main results

* `exists_good_multiplier_zmod` : the finite-torus multiplier avoidance theorem.
* `exists_good_multiplier_int` : an integer-displacement corollary, where each
  vector has a coordinate not divisible by `p`.
-/


open Finset

namespace TorusMultiplierAvoidance

variable {p : ℕ} [Fact p.Prime]

/-- The set of multipliers `a` that "kill" the displacement `d`, i.e. for which
the dot product `d.1 * a.1 + d.2 * a.2` vanishes. -/
def bad (d : ZMod p × ZMod p) : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter fun a => d.1 * a.1 + d.2 * a.2 = 0

/-
A nonzero displacement vector's bad set is a line: it has at most `p`
multipliers.
-/

/-
The finite-torus multiplier avoidance theorem: if `D` is a set of nonzero
displacement vectors over `ZMod p` with `D.card < p`, then some multiplier `a`
gives a nonzero dot product with every `d ∈ D`.
-/

/-
Integer-displacement corollary.  If `E` is a set of integer displacement
vectors, each having at least one coordinate not divisible by `p`, and
`E.card < p`, then there is a multiplier `a : ZMod p × ZMod p` whose reduced dot
product with every `e ∈ E` is nonzero.  This connects the finite theorem to
lacunary-distance multiplier constructions.
-/

end TorusMultiplierAvoidance


