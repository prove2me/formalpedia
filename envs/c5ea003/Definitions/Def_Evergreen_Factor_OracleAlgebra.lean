-- Prove2me | Definitions.Def_Evergreen_Factor_OracleAlgebra
-- name    : Evergreen_Factor_OracleAlgebra
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T16:36:54.798367+00:00
-- url     : https://prove2.me/theorems/b5069d81-3da5-4644-9450-c3b3b2e5141a
-- title:
--   Aether Catalog definitions — Evergreen_Factor_OracleAlgebra
-- statement:
--   Definition bundle for the Aether Catalog module `Evergreen.Factor.OracleAlgebra`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Evergreen/Factor/OracleAlgebra.lean by skeleton subtraction
import Mathlib

/-!
# Oracle Algebra: Lattices, Monoids, and Galois Connections

## Beyond Flatland Part III — Algebraic Structures

This file develops the algebraic theory of oracle operators, showing they form
rich structures: partial orders, lattices, and connections to Galois theory.
-/

open Finset Function Set

/-! ## Section 5: The Oracle Partial Order

Oracles can be ordered by refinement: O₁ ≤ O₂ if truthSet(O₂) ⊆ truthSet(O₁),
meaning O₁ is "more accepting" than O₂. We explore this ordering.
-/

/-- An oracle is an idempotent function. -/
def IsOracle' {α : Type*} (O : α → α) : Prop := ∀ x, O (O x) = O x

/-- Truth set of an oracle. -/
def oracleTruth {α : Type*} (O : α → α) : Set α := {x | O x = x}









/-! ## Section 6: Oracle Monoid Structure

The set of all oracles on a type, under composition, forms a monoid
when we restrict to commuting families.
-/

/-
Theorem 21.1: The identity is an oracle.
-/





/-! ## Section 7: The Modular Oracle Hierarchy

The modular oracle mod n maps ℤ → ℤ via x ↦ x % n. We study the hierarchy
of these oracles across different moduli.
-/

/-- The modular oracle: reduction mod n. -/
def modOracle (n : ℕ) (x : ℤ) : ℤ := x % (n : ℤ)







/-! ## Section 8: Oracle Galois Connections

Oracles naturally give rise to Galois connections between the poset of
subsets and the poset of oracles.
-/





/-! ## Section 9: Boolean Oracle Algebra

On a finite Boolean type, oracles correspond to choosing a subset and
projecting onto it.
-/

/-
Theorem 24.1: On Bool, there are exactly 3 oracles:
    id, const true, const false. We verify each.
-/


