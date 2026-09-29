-- Prove2me | Theorems.Thm_TangledHierarchies_isTangled_of_selfLoop
-- name    : TangledHierarchies.isTangled_of_selfLoop
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:45:36.628894+00:00
-- url     : https://prove2.me/theorems/e6425c79-61bd-48eb-b1c2-03b81ea2c666
-- title:
--   Every self-loop is a tangle (take `x = y`).
-- statement:
--   Every self-loop is a tangle (take `x = y`).
--
--   ```lean
--   theorem TangledHierarchies.isTangled_of_selfLoop{r : α → α → Prop} (h : HasSelfLoop r) : IsTangled r := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/TangledHierarchies.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/TangledHierarchies.lean#L51

-- Thm stub generated from Logic/TangledHierarchies.lean
import Mathlib
import Definitions.Def_Logic_StrangeLoops_Core
import Definitions.Def_Logic_TangledHierarchies
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


open TangledHierarchies

universe u

variable {α : Type u}

/-! ## Part 1 — Tangles and cycles -/

theorem TangledHierarchies.isTangled_of_selfLoop{r : α → α → Prop} (h : HasSelfLoop r) : IsTangled r := by sorry
