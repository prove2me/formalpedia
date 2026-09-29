-- Prove2me | Definitions.Def_Geometry_KernelPatterns_Chambers
-- name    : Geometry_KernelPatterns_Chambers
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:37:00.063416+00:00
-- url     : https://prove2.me/theorems/7b55e431-228d-4e43-9a0b-117f01f045c4
-- title:
--   Aether Catalog definitions — Geometry_KernelPatterns_Chambers
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.KernelPatterns.Chambers`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/KernelPatterns/Chambers.lean by skeleton subtraction
import Mathlib

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

namespace Geometry.KernelPatterns

open Finset

variable {n : ℕ}

/-- The open chamber of the braid arrangement in `ℝ^n` indexed by a permutation:
the coordinates are strictly increasing along `σ`. -/
def chamber (n : ℕ) (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  {v | ∀ i j : Fin n, i < j → v (σ i) < v (σ j)}









/-- The set of chambers of the braid arrangement. -/
def chambers (n : ℕ) : Set (Set (Fin n → ℝ)) := Set.range (chamber n)


end Geometry.KernelPatterns


