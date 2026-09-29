-- Prove2me | Definitions.Def_Bridges_MatroidMinorFiniteBasis
-- name    : Bridges_MatroidMinorFiniteBasis
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:28:58.985636+00:00
-- url     : https://prove2.me/theorems/2661923e-1f48-4ce9-bde1-2310fa7c74c0
-- title:
--   Aether Catalog definitions — Bridges_MatroidMinorFiniteBasis
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.MatroidMinorFiniteBasis`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/MatroidMinorFiniteBasis.lean by skeleton subtraction
import Mathlib
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

namespace MatroidMinorFiniteBasis

section OrderTheory

variable {α : Type*} [PartialOrder α]

/-- The minimal members of a set in a partial order. -/
def minimalMembers (U : Set α) : Set α :=
  {x | x ∈ U ∧ ∀ y, y < x → y ∉ U}









end OrderTheory

section Matroids

open Matroid

variable {α : Type*}

/-- A class of matroids is minor-closed when it contains every minor of each of
its members. -/
def IsMatroidMinorClosed (C : Set (Matroid α)) : Prop :=
  ∀ ⦃M N : Matroid α⦄, M ∈ C → N ≤m M → N ∈ C

/-- A matroid is an excluded minor for `C` when it is outside `C` and every
strictly smaller minor belongs to `C`. -/
def IsExcludedMinor (C : Set (Matroid α)) (M : Matroid α) : Prop :=
  M ∉ C ∧ ∀ ⦃N : Matroid α⦄, N <m M → N ∈ C






end Matroids

end MatroidMinorFiniteBasis


