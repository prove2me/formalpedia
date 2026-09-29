-- Prove2me | Theorems.Thm_RecipeHomotopy_InterchangeStructure_vcomp_assoc
-- name    : RecipeHomotopy.InterchangeStructure.vcomp_assoc
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:09:20.882268+00:00
-- url     : https://prove2.me/theorems/6a0e7782-9616-4bff-b1cd-581d8c093fb2
-- title:
--   The (common) composition is associative.
-- statement:
--   The (common) composition is associative.
--
--   ```lean
--   theorem RecipeHomotopy.InterchangeStructure.vcomp_assoc(a b c : α) :
--       S.vcomp (S.vcomp a b) c = S.vcomp a (S.vcomp b c) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/RecipeHomotopyEckmannHilton.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/RecipeHomotopyEckmannHilton.lean#L109

-- Thm stub generated from Bridges/RecipeHomotopyEckmannHilton.lean
import Mathlib
import Definitions.Def_Bridges_RecipeHomotopyEckmannHilton

/-!
# A Bridge between Topology and Algebra: the Eckmann–Hilton argument

## The cross-domain connection

This file proves a genuine *connector* theorem linking two areas that look
unrelated at first sight:

* **Topology / homotopy theory.** In a homotopy type the loops based at a point
  can be composed. When one moves to *2-dimensional* structure (loops between
  loops, i.e. the second homotopy group `π₂`, or loops in a topological monoid /
  H-space) there are genuinely *two* ways to compose: a "vertical" composition
  and a "horizontal" composition. They share a common identity (the constant
  loop) and satisfy the *interchange law*.

* **Algebra.** A commutative monoid.

The **Eckmann–Hilton argument** says these two worlds coincide: any set carrying
two unital binary operations that share the same unit and satisfy the
interchange law is forced to have the two operations *equal*, and that single
operation is automatically **commutative and associative**.  This is the abstract
reason why the higher homotopy groups `πₙ` (`n ≥ 2`) are abelian, and why the
fundamental group of a topological group is abelian.  A purely *topological*
input (two ways to compose loops) produces a purely *algebraic* output (a
commutative monoid) — no continuity, no analysis, only the interchange law.

## The "recipe / homotopy of dishes" narrative

Think of the points as *dishes* (flavor profiles) and of the two operations as
two different ways of combining cooking procedures: e.g. combining two recipes
"in series" (do one method after the other) versus "in parallel" (blend two
methods into one). The interchange law says that combining-in-series a pair of
parallel blends equals combining-in-parallel a pair of serial blends. The
Eckmann–Hilton theorem then says: whenever both ways of combining share a
trivial "do nothing" recipe, the two ways of combining are the *same* way, and
the resulting operation on dishes is commutative and associative. Cooking, at the
level of methods, is a commutative monoid.

## Main results

* `InterchangeStructure` — the data of two unital operations with a shared unit
  satisfying the interchange law.
* `InterchangeStructure.hcomp_eq_vcomp` — the two operations coincide.
* `InterchangeStructure.vcomp_comm` — the operation is commutative.
* `InterchangeStructure.vcomp_assoc` — the operation is associative.
* `InterchangeStructure.toCommMonoid` — package the raw data into a
  `CommMonoid`, realizing the topology → algebra bridge.
* `InterchangeStructure.ofCommMonoid` — every commutative monoid gives an
  interchange structure (with both operations equal to `*`), so the hypotheses
  are non-vacuous and the correspondence is genuine.
-/

open RecipeHomotopy


open InterchangeStructure

variable {α : Type*} (S : InterchangeStructure α)

theorem RecipeHomotopy.InterchangeStructure.vcomp_assoc(a b c : α) :
    S.vcomp (S.vcomp a b) c = S.vcomp a (S.vcomp b c) := by sorry
