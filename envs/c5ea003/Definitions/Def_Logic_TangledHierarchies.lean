-- Prove2me | Definitions.Def_Logic_TangledHierarchies
-- name    : Logic_TangledHierarchies
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:03:46.532391+00:00
-- url     : https://prove2.me/theorems/e70a6e75-c55b-4a4a-a920-2b0fd8423a8e
-- title:
--   Aether Catalog definitions — Logic_TangledHierarchies
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.TangledHierarchies`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/TangledHierarchies.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_StrangeLoops_Core
/-
# Tangled Hierarchies: Order, Grading, and the Inconsistency of the Ultimate Tangle

A *tangled hierarchy* is a level structure in which some pair of elements sits both
above and below one another — a two-cycle `x ≺ y` and `y ≺ x`.  Hofstadter's
"strange loops" are the informal picture; here we give the order-theoretic core and
draw a sharp line between hierarchies that *can* be tangled and hierarchies that
*cannot*.

The central findings of this cycle are:

* **Well-founded hierarchies are never tangled.**  In particular the ladder of
  levels modelled by `(ℕ, <)` — the abstract shape of the tower
  `level₀ ≺ level₁ ≺ level₂ ≺ ⋯` — carries no tangle.
* **A grading forbids tangles.**  Any relation that admits an integer *rank*
  strictly increasing along every edge is untangled.  Contrapositively, a genuinely
  tangled hierarchy admits *no* consistent level assignment: one must abandon either
  the tangle or the grading.  This is the crisp form of the informal conjecture that
  a consistent tangled hierarchy costs you either consistency or the hierarchy.
* **Apparent tangles from adjacency.**  Allowing each level to "refer to" its
  neighbours produces a symmetric adjacency relation that *is* tangled, even though
  the underlying level order is not — the polymorphic "a term at level `n` may
  mention level `n+1`" phenomenon, seen from the graph side.
* **The ultimate tangle is inconsistent.**  A universe that reflects its own full
  power set — an element for every predicate over itself — cannot exist.  This is the
  Cantor/Girard heart of "`Type : Type`", proved here by a self-contained diagonal
  argument and, in a bridge result, from the catalog's Lawvere fixed-point theorem.

## Relationship to catalog
* Complements `Logic.StrangeLoops.Core` (Lawvere/Gödel view of tangled hierarchies)
  with the order-theoretic and grading view, and reuses its `cantor_from_lawvere`.
-/


namespace TangledHierarchies

universe u

variable {α : Type u}

/-! ## Part 1 — Tangles and cycles -/

/-- A relation is **tangled** when some pair lies both above and below the other:
a two-cycle `r x y ∧ r y x`.  This is the minimal formal shape of a "strange loop". -/
def IsTangled (r : α → α → Prop) : Prop := ∃ x y, r x y ∧ r y x

/-- A **self-loop** `r x x` is the degenerate one-element tangle. -/
def HasSelfLoop (r : α → α → Prop) : Prop := ∃ x, r x x




/-! ## Part 2 — Well-founded hierarchies carry no tangle -/




/-! ## Part 3 — Grading: the price of a consistent tangle -/



/-! ## Part 4 — Apparent tangles from adjacency (polymorphic reference) -/

/-- The **adjacency** relation on levels: a level may refer to the level immediately
above or below it.  This models the polymorphic phenomenon "a term at level `n` may
mention level `n+1`" purely on the reference graph. -/
def refersAdjacent (n m : ℕ) : Prop := m = n + 1 ∨ n = m + 1





/-! ## Part 5 — The ultimate tangle: a self-reflecting universe is inconsistent -/


/-- A **reflective universe**: a type `U` together with a decoding of each element as
a predicate over `U`, such that *every* predicate over `U` is named by some element.
This is the ultimate tangle — a universe reflecting its own full power set, the shape
of "`Type : Type`". -/
structure ReflectiveUniverse (U : Type u) where
  /-- Each code names a subset of the universe. -/
  decode : U → Set U
  /-- Every subset of the universe has a code: the universe reflects its power set. -/
  complete : Function.Surjective decode



/-! ## Part 6 — Bridge to the catalog's Lawvere machinery -/


end TangledHierarchies

-- !-- Lab Notes -- !--
--
-- Hypothesis (Hypothesizer):
--   A "tangled hierarchy" (Hofstadter) — an order with a two-cycle x ≺ y, y ≺ x —
--   cannot coexist with a well-founded level structure. We conjectured a sharp
--   dichotomy: a hierarchy is either *graded* (carries an increasing ℕ-rank) or it
--   is *tangled*, never both; and that the maximal tangle (a universe reflecting its
--   own power set, the shape of `Type : Type`) is outright inconsistent.
--
-- Experiment (Experimenter):
--   • `IsTangled` captures the two-cycle. `asymmetric_not_tangled` and
--     `wellFounded_not_tangled` show orders/well-founded relations avoid tangles;
--     `universeLevels_not_tangled` instantiates this at `(ℕ, <)`.
--   • `graded_not_tangled` (proof: `omega` on `rank x < rank y < rank x`) is the
--     structural core; `tangled_has_no_grading` is its contrapositive.
--   • `refersAdjacent` witnesses a genuine tangle living atop the untangled ladder,
--     and `symmetric_isTangled` explains why (symmetry ⇒ two-cycle).
--   • `no_surjective_to_powerset` (self-contained diagonal) yields
--     `no_reflectiveUniverse`; `reflectiveUniverse_russell` exhibits the explicit
--     self-membership fixed point; `no_propReflectiveUniverse` re-derives the
--     Prop-valued case from the catalog's `cantor_from_lawvere`.
--
-- Analysis (Analyst):
--   Survived: all six main results. The unifying pattern is that *rank* (a grading)
--   is exactly the resource a tangle consumes — a two-cycle forces a strict integer
--   descent into itself, which `omega` refutes. The Cantor/Girard collapse is the
--   same obstruction one cardinal higher: no carrier ranks its own power set.
--   Failure mode noticed and avoided: stating the tangle as mere reflexivity would
--   trivialize it; requiring two distinct-role edges keeps the adjacency example
--   informative.
--
-- Critique (Critic):
--   No theorem is vacuous: `refersAdjacent_isTangled` gives a concrete inhabitant,
--   and the impossibility results have nonempty hypotheses (a surjection/structure)
--   that are refuted, not assumed away. No proof references itself. Axioms are the
--   standard `propext/Classical.choice/Quot.sound` only; `universeLevels_not_tangled`
--   and `reflectiveUniverse_russell` are axiom-free.
--
-- Synthesis (PI):
--   The order-theoretic view complements `Logic.StrangeLoops.Core`: strange loops are
--   precisely relations with no ℕ-grading, and the ultimate loop is Cantor-forbidden.
--   See `FUTURE_DIRECTIONS.md` for the next-cycle conjectures (ordinal-valued ranks,
--   n-cycles, and stratified reflection).
-- !-- Lab Notes -- !--


