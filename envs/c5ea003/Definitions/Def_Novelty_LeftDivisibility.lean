-- Prove2me | Definitions.Def_Novelty_LeftDivisibility
-- name    : Novelty_LeftDivisibility
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:32:03.048889+00:00
-- url     : https://prove2.me/theorems/a5032398-c2d0-49d8-999a-058b7dcf5ed1
-- title:
--   Aether Catalog definitions — Novelty_LeftDivisibility
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.LeftDivisibility`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/LeftDivisibility.lean by skeleton subtraction
import Mathlib
/-
# Left-divisibility orders, LCIF monoids, and the upho prototype

This file develops the *order-theoretic* half of the research mission
**"Multiplicability of Upho Posets from Vertex-Transitive Graphs"**.

The mission's notion of **multiplicability** is: an upho poset `P` is multiplicable
iff it carries an **LCIF monoid** structure (Left-Cancellative, Identity-Free of
nontrivial units, locally finite) whose **left-divisibility order**
`a ≼ b ⟺ ∃ c, b = a * c` recovers the poset order of `P`.

This file isolates and proves the structural facts about left-divisibility that
make this definition meaningful:

* `LeftDvd` is always a **preorder** (reflexive + transitive) on any monoid.
* In a **group**, left-divisibility *collapses*: every element divides every
  other, so the induced order is the indiscrete one.  Consequently the order is
  a genuine partial order (antisymmetric) **iff the group is trivial**
  (`group_leftDvd_antisymm_iff_subsingleton`).  This is exactly why the
  *automorphism group* of a vertex-transitive graph cannot itself be the upho
  poset — the grading must come from elsewhere.
* The **free monoid** on an alphabet (= words = walks) is the canonical LCIF
-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer).  Multiplicability is fundamentally an order condition:
"left-divisibility recovers the poset".  Conjecture: groups are the *wrong*
monoid (their divisibility order is trivial) while free monoids are the *right*
prototype (prefix order = upho poset).  Bold sub-conjecture: antisymmetry of
left-divisibility in a group is equivalent to triviality.

EXPERIMENT (Experimenter).  We defined `LeftDvd` and verified reflexivity and
transitivity directly.  For groups we found `b = a * (a⁻¹ * b)` collapses the
order; for free monoids `List.IsPrefix` and `List.inits` deliver antisymmetry and
finitariness.

ANALYSIS (Analyst).  Survived: preorder laws, group collapse, the
antisymmetry↔subsingleton dichotomy, free-monoid partial order + finitariness.
Structural insight: *cancellativity + absence of nontrivial units* is precisely
what upgrades the preorder to a partial order; groups maximally violate the
second (every element is a unit), free monoids maximally satisfy it.

CRITIQUE (Critic).  We were careful that `LeftDvd` matches Mathlib's `IsPrefix`
only up to the orientation of the defining equation, and proved the bridge lemma
`freeMonoid_leftDvd_iff_isPrefix` rather than assuming it.  The group dichotomy is
an honest iff, not a one-way triviality.

SYNTHESIS (PI).  These give the LCIF/order scaffolding; see `FUTURE_DIRECTIONS.md`
for the conjectural fusion with the Sabidussi/regular-subgroup side.
-/

namespace UphoMultiplicability

/-- **Left-divisibility**: `a` left-divides `b` when `b = a * c` for some `c`. -/
def LeftDvd {M : Type*} [Monoid M] (a b : M) : Prop := ∃ c, b = a * c




/-! ## Groups: the order collapses -/



/-! ## Free monoids: the upho prototype -/





end UphoMultiplicability


