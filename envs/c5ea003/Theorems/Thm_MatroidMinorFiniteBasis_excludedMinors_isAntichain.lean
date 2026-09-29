-- Prove2me | Theorems.Thm_MatroidMinorFiniteBasis_excludedMinors_isAntichain
-- name    : MatroidMinorFiniteBasis.excludedMinors_isAntichain
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:56:12.865819+00:00
-- url     : https://prove2.me/theorems/964adc93-8901-4359-ba3a-b15607f141b3
-- title:
--   Distinct excluded minors of a class are incomparable by the minor relation.
-- statement:
--   Distinct excluded minors of a class are incomparable by the minor relation.
--
--   ```lean
--   theorem MatroidMinorFiniteBasis.excludedMinors_isAntichain(C : Set (Matroid α)) :
--       IsAntichain (· ≤m ·) {M | IsExcludedMinor C M} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/MatroidMinorFiniteBasis.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/MatroidMinorFiniteBasis.lean#L140

-- Thm stub generated from Bridges/MatroidMinorFiniteBasis.lean
import Mathlib
import Definitions.Def_Bridges_MatroidMinorFiniteBasis
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

/-!
# Well-quasi-orders and finite excluded-minor bases

This file formalizes the order-theoretic implication at the heart of the proposed
Robertson--Seymour theorem for finite-field-representable matroids.  It does not
assert that representable matroids are well-quasi-ordered.  Instead, it proves
that any such well-quasi-order theorem would yield a finite excluded-minor
characterization.

The development applies to an arbitrary partial order, and is then stated in the
language of the matroid minor order.  The finite obstruction set is canonical:
it consists of the minimal objects outside the minor-closed class.
-/

open Set

open MatroidMinorFiniteBasis


variable {α : Type*} [PartialOrder α]












open Matroid

variable {α : Type*}

theorem MatroidMinorFiniteBasis.excludedMinors_isAntichain(C : Set (Matroid α)) :
    IsAntichain (· ≤m ·) {M | IsExcludedMinor C M} := by sorry
