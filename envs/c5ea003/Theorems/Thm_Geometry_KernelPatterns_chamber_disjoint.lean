-- Prove2me | Theorems.Thm_Geometry_KernelPatterns_chamber_disjoint
-- name    : Geometry.KernelPatterns.chamber_disjoint
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:19:59.460976+00:00
-- url     : https://prove2.me/theorems/8559e563-ac07-44d4-b384-e386ca507622
-- title:
--   Distinct permutations give disjoint chambers: an injective tuple is sorted
-- statement:
--   Distinct permutations give disjoint chambers: an injective tuple is sorted
--   by exactly one permutation.
--
--   ```lean
--   theorem Geometry.KernelPatterns.chamber_disjoint{σ τ : Equiv.Perm (Fin n)} (hne : σ ≠ τ) :
--       Disjoint (chamber n σ) (chamber n τ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/KernelPatterns/Chambers.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/KernelPatterns/Chambers.lean#L91

-- Thm stub generated from Geometry/KernelPatterns/Chambers.lean
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

theorem Geometry.KernelPatterns.chamber_disjoint{σ τ : Equiv.Perm (Fin n)} (hne : σ ≠ τ) :
    Disjoint (chamber n σ) (chamber n τ) := by sorry
