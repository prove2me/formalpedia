-- Prove2me | solution 1 for Catalog.DerivedFunctors.qShortComplex_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:06:10.414372+00:00
-- url     : https://prove2.me/submissions/1567ec50-d093-4455-b96c-23793d9dc8ee

-- Sol generated from Algebra/DerivedFunctors/Resolutions.lean
import Mathlib
import Definitions.Def_Algebra_DerivedFunctors_Resolutions

/-!
# Concrete projective and injective resolutions

This file constructs two concrete resolutions in the category of `ℤ`-modules
(equivalently, abelian groups):

* `Catalog.DerivedFunctors.zmodShortComplex k`: the short exact sequence
  `0 → ℤ --(·k)--> ℤ --(mod k)--> ZMod k → 0`, which is the standard length-one
  free (hence projective) resolution of the cyclic group `ZMod k` for `k ≠ 0`.

These are used in `Algebra.DerivedFunctors.Ext` to compute `Ext`-groups.
-/

universe u

open CategoryTheory Abelian Limits

open Catalog.DerivedFunctors


variable (k : ℕ)


























open Catalog.DerivedFunctors in
theorem solution: qShortComplex.ShortExact where
  exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hx' : (show ℚ from x) ∈ AddSubgroup.zmultiples (1 : ℚ) := by
      have h : (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))) (show ℚ from x) = 0 := hx
      simpa [QuotientAddGroup.eq_zero_iff] using h
    obtain ⟨n, hn⟩ := hx'
    exact ⟨n, by simpa using hn⟩
  mono_f := (ModuleCat.mono_iff_injective _).2 (by
    intro a b h
    have h' : ((show ℤ from a : ℤ) : ℚ) = ((show ℤ from b : ℤ) : ℚ) := h
    exact_mod_cast h')
  epi_g := (ModuleCat.epi_iff_surjective _).2 QuotientAddGroup.mk_surjective
