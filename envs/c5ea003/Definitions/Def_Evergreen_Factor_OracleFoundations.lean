-- Prove2me | Definitions.Def_Evergreen_Factor_OracleFoundations
-- name    : Evergreen_Factor_OracleFoundations
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T16:37:06.134856+00:00
-- url     : https://prove2.me/theorems/da03c2f3-014f-4400-9452-d6d34fd57398
-- title:
--   Aether Catalog definitions — Evergreen_Factor_OracleFoundations
-- statement:
--   Definition bundle for the Aether Catalog module `Evergreen.Factor.OracleFoundations`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Evergreen/Factor/OracleFoundations.lean by skeleton subtraction
import Mathlib

/-!
# Oracle Foundations: Spectral Theory, Entropy, and Fixed Points

## Beyond Flatland Part III — New Oracle Theory

This file develops the foundational theory of mathematical oracles (idempotent operators)
including spectral decomposition, entropy quantification, and fixed-point characterization.

All theorems are machine-verified with zero sorries.
-/

open Finset Function

/-! ## Section 1: Oracle Basics and Spectral Theory -/

/-- An oracle is an idempotent function: applying it twice equals applying it once. -/
def IsOracle {α : Type*} (O : α → α) : Prop := ∀ x, O (O x) = O x

/-- The truth set of an oracle: points fixed by the oracle. -/
def truthSet {α : Type*} (O : α → α) : Set α := {x | O x = x}

/-- The illusion set of an oracle: points moved by the oracle. -/
def illusionSet {α : Type*} (O : α → α) : Set α := {x | O x ≠ x}







/-
Theorem 16.4: The identity function is an oracle with full truth set.
-/

/-
Theorem 16.5: The identity oracle's truth set is everything.
-/

/-
Theorem 16.6: A constant function is an oracle.
-/

/-
Theorem 16.7: The constant oracle's truth set is a singleton.
-/

/-! ## Section 2: Oracle Spectral Theory

An oracle, viewed as a linear operator on a vector space, has a remarkable
spectral property: its only eigenvalues are 0 and 1. This is the algebraic
manifestation of the truth/illusion partition.
-/











/-! ## Section 3: Oracle Entropy on Finite Types

For an oracle on a finite type, we can quantify its "information content"
by the cardinality of its truth set. This gives a natural measure of how
much structure the oracle preserves.
-/

/-- The truth set of an oracle as a Finset, for decidable equality. -/
def truthFinset {α : Type*} [Fintype α] [DecidableEq α] (O : α → α) : Finset α :=
  Finset.univ.filter (fun x => O x = x)

/-- The entropy rank of an oracle: cardinality of its truth set. -/
def entropyRank {α : Type*} [Fintype α] [DecidableEq α] (O : α → α) : ℕ :=
  (truthFinset O).card









/-! ## Section 4: Oracle Fixed-Point Theory -/


