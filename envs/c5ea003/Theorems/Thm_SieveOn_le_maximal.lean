-- Prove2me | Theorems.Thm_SieveOn_le_maximal
-- name    : SieveOn.le_maximal
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-16T20:33:38.626316+00:00
-- url     : https://prove2.me/theorems/84279b62-a3a0-4422-9d89-68485fcf9ab5
-- title:
--   The maximal sieve is the top element.
-- statement:
--   The maximal sieve is the top element.
--
--   ```lean
--   theorem SieveOn.le_maximal(d : α) (s : SieveOn α d) : s ≤ maximal d := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/Foundations.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/Foundations.lean#L146

-- Thm stub generated from Bridges/ToposTheoreticML/Foundations.lean
import Mathlib
import Definitions.Def_Bridges_ToposTheoreticML_Foundations

/-! # Topos-Theoretic Machine Learning: Foundations

This file develops the shared vocabulary connecting statistical learning theory to
topos-theoretic geometry.  It introduces concept families and their shattering /
Vapnik–Chervonenkis dimension, the Sauer–Shelah growth function, an abstract
sample-complexity functional, sieves on a preorder together with their lattice
structure, and the auxiliary data (cryptographic hardness witnesses, transfer
morphisms) used to phrase transfer and lower-bound results.

The downstream file `Bridges/VCCompactness.lean` builds the actual bridge theorems
on top of these definitions.
-/

-- open removed: section is not a namespace

/-! ## Concept families, shattering and VC dimension -/


open ConceptFamily

variable {α : Type*}






/-! ## The Sauer–Shelah growth function -/



/-! ## Sample complexity -/




/-! ## Sieves on a preorder and their lattice structure -/


open SieveOn

variable {α : Type*} [Preorder α] {d : α}

theorem SieveOn.le_maximal(d : α) (s : SieveOn α d) : s ≤ maximal d := by sorry
