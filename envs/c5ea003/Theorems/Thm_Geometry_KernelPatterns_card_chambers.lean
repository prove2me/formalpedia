-- Prove2me | Theorems.Thm_Geometry_KernelPatterns_card_chambers
-- name    : Geometry.KernelPatterns.card_chambers
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:20:04.753538+00:00
-- url     : https://prove2.me/theorems/029a1db9-312f-4be7-861e-dd20cb464238
-- title:
--   The braid arrangement in `ℝ^n` has `n !` chambers (compare
-- statement:
--   **The braid arrangement in `ℝ^n` has `n !` chambers** (compare
--   `card_braidFlats_eq_bell`: it has `Nat.bell n` flats).
--
--   ```lean
--   theorem Geometry.KernelPatterns.card_chambers(n : ℕ) : Nat.card (chambers n) = Nat.factorial n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/KernelPatterns/Chambers.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/KernelPatterns/Chambers.lean#L139

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

theorem Geometry.KernelPatterns.card_chambers(n : ℕ) : Nat.card (chambers n) = Nat.factorial n := by sorry
