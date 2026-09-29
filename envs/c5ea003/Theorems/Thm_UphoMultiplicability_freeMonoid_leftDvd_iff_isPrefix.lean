-- Prove2me | Theorems.Thm_UphoMultiplicability_freeMonoid_leftDvd_iff_isPrefix
-- name    : UphoMultiplicability.freeMonoid_leftDvd_iff_isPrefix
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:40:35.210818+00:00
-- url     : https://prove2.me/theorems/851b8e3f-f836-428f-a7b3-29308dfd0a19
-- title:
--   Left-divisibility in a free monoid is exactly the prefix relation on words.
-- statement:
--   Left-divisibility in a free monoid is exactly the prefix relation on words.
--
--   ```lean
--   theorem UphoMultiplicability.freeMonoid_leftDvd_iff_isPrefix{α : Type*} (a b : FreeMonoid α) :
--       LeftDvd a b ↔ (a : List α) <+: (b : List α) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/LeftDivisibility.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/LeftDivisibility.lean#L101

-- Thm stub generated from Novelty/LeftDivisibility.lean
import Mathlib
import Definitions.Def_Novelty_LeftDivisibility
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
  example: its left-divisibility order is the **prefix order**, which is a
  partial order (`freeMonoid_leftDvd_antisymm`) and is **finitary**
  (`freeMonoid_leftDvd_finitary`: every element has only finitely many
  left-divisors).  This is the prototype of a finitary upho poset.

Together with `Sabidussi.lean`, the picture is: a Cayley structure (regular
group action, the *symmetry* side) plus a free/walk monoid (the *grading*,
LCIF/order side) is what an upho poset needs to be multiplicable.

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

open UphoMultiplicability





/-! ## Groups: the order collapses -/



/-! ## Free monoids: the upho prototype -/

theorem UphoMultiplicability.freeMonoid_leftDvd_iff_isPrefix{α : Type*} (a b : FreeMonoid α) :
    LeftDvd a b ↔ (a : List α) <+: (b : List α) := by sorry
