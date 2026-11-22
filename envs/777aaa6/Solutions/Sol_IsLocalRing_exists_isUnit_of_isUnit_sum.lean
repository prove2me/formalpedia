-- Prove2me | solution 1 for IsLocalRing.exists_isUnit_of_isUnit_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:54:20.662806+00:00
-- url     : https://prove2.me/submissions/b5ace5c9-4e89-47d6-85cf-740627154bf7

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.DoubleCoset
import Definitions.Def_BruhatTits_Utils_Misc

set_option autoImplicit false
variable {α β γ : Type*}
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
namespace IsLocalRing
theorem _root_.solution {ι R : Type*} [CommRing R] [IsLocalRing R]
    {s : Finset ι} {f : ι → R} (h : IsUnit (∑ i ∈ s, f i)) : ∃ i ∈ s, IsUnit (f i) := by
  contrapose! h
  simp_rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal] at h ⊢
  exact Ideal.sum_mem (maximalIdeal R) h
end IsLocalRing
