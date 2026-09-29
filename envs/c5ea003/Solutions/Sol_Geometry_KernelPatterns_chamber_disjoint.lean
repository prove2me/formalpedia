-- Prove2me | solution 1 for Geometry.KernelPatterns.chamber_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:52:35.17221+00:00
-- url     : https://prove2.me/submissions/68453446-519e-4ee9-a5fc-1443eebd2cce

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
theorem solution{σ τ : Equiv.Perm (Fin n)} (hne : σ ≠ τ) :
    Disjoint (chamber n σ) (chamber n τ) := by
  rw [Set.disjoint_left]
  intro v hσ hτ
  apply hne
  have hmono : StrictMono fun i => v (σ i) := fun i j hij => hσ i j hij
  have hmono' : StrictMono fun i => v (τ i) := fun i j hij => hτ i j hij
  set ρ : Equiv.Perm (Fin n) := τ.trans σ.symm with hρdef
  have hρapp : ∀ i, ρ i = σ.symm (τ i) := fun i => rfl
  have hρ : StrictMono (ρ : Fin n → Fin n) := by
    intro i j hij
    have h1 : v (σ (ρ i)) < v (σ (ρ j)) := by
      simpa [hρapp] using hmono' hij
    exact hmono.lt_iff_lt.1 h1
  have hρsymm : StrictMono (ρ.symm : Fin n → Fin n) := by
    intro i j hij
    by_contra hle
    push_neg at hle
    have hmon := hρ.monotone hle
    simp only [Equiv.apply_symm_apply] at hmon
    exact absurd hij (not_lt.2 hmon)
  have hid : ∀ i, ρ i = i := by
    intro i
    have h2 : i ≤ ρ.symm i := hρsymm.le_apply
    have h3 : ρ i ≤ i := by
      have := hρ.monotone h2
      simpa using this
    exact le_antisymm h3 hρ.le_apply
  refine Equiv.ext fun i => ?_
  have := hid i
  rw [hρapp] at this
  have := congrArg σ this
  simpa using this.symm
