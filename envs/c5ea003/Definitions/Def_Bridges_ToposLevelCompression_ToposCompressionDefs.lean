-- Prove2me | Definitions.Def_Bridges_ToposLevelCompression_ToposCompressionDefs
-- name    : Bridges_ToposLevelCompression_ToposCompressionDefs
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:40:54.53495+00:00
-- url     : https://prove2.me/theorems/389ba56d-c1ac-49ee-a2ef-306c361da607
-- title:
--   Aether Catalog definitions — Bridges_ToposLevelCompression_ToposCompressionDefs
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ToposLevelCompression.ToposCompressionDefs`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ToposLevelCompression/ToposCompressionDefs.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harmonic Research
-/

/-!
# Topos-Level Compression — Definitions

This file defines the core objects of the **probe compression** framework
for finite presheaf-like models.

## Main Definitions

* `ProbeFamily` — a `Finset` of "probe objects" used to distinguish sections.
* `probeSignature'` — the signature of a section at all probe objects.
* `ProbeSeparates` — a probe family separates if signatures are injective at every object.
* `ProbeSeparating'` — global separation: there exists a separating family.
* `compressionSpectrum'` — the set of cardinalities of separating families.
* `presheafMinCompression'` — the minimum cardinality of a separating family.
* `realizesCompression'` — a natural number is realized if some family of that size separates.
* `representableDim` — the sum of fiber cardinalities.
* `fiberObsComplexity` — fiber-level observation complexity.
* `observationComplexity'` — the maximum fiber observation complexity.
* `CompressionEquiv` — compression-compatible equivalence between two models.
-/

open Finset Fintype

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u v w

/-- A probe family is a `Finset` of objects. -/
abbrev ProbeFamily (Ob : Type*) := Finset Ob

variable {Ob : Type u} [Fintype Ob] [DecidableEq Ob]

/-- The **probe signature** of a section `s ∈ F(Y)` relative to a probe family `P`:
for each probe object `Z ∈ P`, apply the restriction map `r Y Z` to `s`. -/
def probeSignature'
    (F : Ob → Type v) (r : ∀ Y Z, F Y → F Z)
    (P : Finset Ob) (Y : Ob) (s : F Y) : ∀ Z : ↥P, F ↑Z :=
  fun ⟨Z, _⟩ => r Y Z s

/-- A probe family `P` **separates** the model `(F, r)` if for every object `Y`,
the probe signature map `F(Y) → ∏_{Z ∈ P} F(Z)` is injective. -/
def ProbeSeparates
    (F : Ob → Type v) (r : ∀ Y Z, F Y → F Z)
    (P : Finset Ob) : Prop :=
  ∀ Y : Ob, Function.Injective (probeSignature' F r P Y)









/-! ### Monotonicity of separation -/


end


