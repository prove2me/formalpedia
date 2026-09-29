-- Prove2me | Theorems.Thm_MatroidMinorFiniteBasis_matroid_wqo_gives_finite_excluded_minors
-- name    : MatroidMinorFiniteBasis.matroid_wqo_gives_finite_excluded_minors
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:56:24.323263+00:00
-- url     : https://prove2.me/theorems/db880e91-4811-417f-b26f-1c0f39dbddaf
-- title:
--   Conditional Robertson--Seymour consequence for matroids: if the matroid
-- statement:
--   Conditional Robertson--Seymour consequence for matroids: if the matroid
--   minor order is a well-quasi-order, every minor-closed class has finitely many
--   excluded minors, and membership is equivalent to avoiding all of them.
--
--   ```lean
--   theorem MatroidMinorFiniteBasis.matroid_wqo_gives_finite_excluded_minors    (hwqo : WellQuasiOrdered ((· ≤m ·) : Matroid α → Matroid α → Prop))
--       (C : Set (Matroid α)) (hC : IsMatroidMinorClosed C) :
--       {M | IsExcludedMinor C M}.Finite ∧
--         ∀ M, M ∈ C ↔ ∀ N, IsExcludedMinor C N → ¬ N ≤m M := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/MatroidMinorFiniteBasis.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/MatroidMinorFiniteBasis.lean#L166

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

theorem MatroidMinorFiniteBasis.matroid_wqo_gives_finite_excluded_minors    (hwqo : WellQuasiOrdered ((· ≤m ·) : Matroid α → Matroid α → Prop))
    (C : Set (Matroid α)) (hC : IsMatroidMinorClosed C) :
    {M | IsExcludedMinor C M}.Finite ∧
      ∀ M, M ∈ C ↔ ∀ N, IsExcludedMinor C N → ¬ N ≤m M := by sorry
