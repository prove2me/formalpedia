-- Prove2me | solution 1 for MatroidMinorFiniteBasis.excludedMinors_isAntichain
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T08:05:15.061304+00:00
-- url     : https://prove2.me/submissions/08686bb5-a026-4ee0-bc37-f37ee564992c

-- Sol generated from Bridges/MatroidMinorFiniteBasis.lean
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


/-- Minimal members of a set are pairwise incomparable.
-/
theorem minimalMembers_isAntichain (U : Set α) :
    IsAntichain (· ≤ ·) (minimalMembers U) := by
  intro x hx y hy hxy;
  exact fun h => hy.2 x ( lt_of_le_of_ne h hxy ) hx.1










open Matroid

variable {α : Type*}



/-- Excluded minors are exactly the order-theoretic minimal members of the
complement.
-/
theorem isExcludedMinor_iff_minimalMember (C : Set (Matroid α)) (M : Matroid α) :
    IsExcludedMinor C M ↔ M ∈ minimalMembers Cᶜ := by
  -- By definition of `IsExcludedMinor`, we have that `M ∉ C` and `∀ ⦃N : Matroid α⦄, N <m M → N ∈ C`.
  simp [IsExcludedMinor, minimalMembers]







open MatroidMinorFiniteBasis in
theorem solution(C : Set (Matroid α)) :
    IsAntichain (· ≤m ·) {M | IsExcludedMinor C M} := by
  intro M hM N hN hMN; have := minimalMembers_isAntichain Cᶜ; simp_all +decide [ IsAntichain ] ;
  exact this ( isExcludedMinor_iff_minimalMember C M |>.1 hM ) ( isExcludedMinor_iff_minimalMember C N |>.1 hN ) hMN
