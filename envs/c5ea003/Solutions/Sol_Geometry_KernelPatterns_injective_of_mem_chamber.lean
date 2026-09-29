-- Prove2me | solution 1 for Geometry.KernelPatterns.injective_of_mem_chamber
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:12:50.463952+00:00
-- url     : https://prove2.me/submissions/e77b1679-129c-4c49-b0bf-d514e94f79b1

-- Sol generated from Geometry/KernelPatterns/Chambers.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Chambers

/-!
# Cycle 2: chambers of the braid arrangement

The kernel pattern of a tuple records *which* coordinates coincide; on the
complement of the braid arrangement — the injective tuples — nothing coincides
and the relevant invariant becomes the *ordering* of the coordinates.  This
file is the chamber-level companion of the flat-level results in
`Geometry.KernelPatterns.BraidFlats`.

* `chamber n σ` — the open cone `v (σ 0) < v (σ 1) < ⋯ < v (σ (n-1))`.
* `chamber_convex`, `chamber_nonempty` — chambers are nonempty convex (hence
  connected) sets.
* `chamber_eq_chamber_iff`, `chamber_injective` — a chamber determines its
  permutation, i.e. the ordering is a complete invariant of the chamber.
* `iUnion_chamber` — the chambers cover exactly the complement of the
  arrangement.
* `card_chambers` — there are `n !` chambers, whereas
  (`card_braidFlats_eq_bell`) there are `Nat.bell n` flats.
-/

open Geometry.KernelPatterns

open Finset

variable {n : ℕ}













open Geometry.KernelPatterns in
theorem solution{σ : Equiv.Perm (Fin n)} {v : Fin n → ℝ}
    (hv : v ∈ chamber n σ) : Function.Injective v := by
  intro x y hxy
  by_contra hne
  have hne' : σ.symm x ≠ σ.symm y := fun h => hne (by
    have := congrArg σ h
    simpa using this)
  rcases lt_or_gt_of_ne hne' with h | h
  · have := hv _ _ h
    simp only [Equiv.apply_symm_apply] at this
    exact absurd hxy (ne_of_lt this)
  · have := hv _ _ h
    simp only [Equiv.apply_symm_apply] at this
    exact absurd hxy.symm (ne_of_lt this)
