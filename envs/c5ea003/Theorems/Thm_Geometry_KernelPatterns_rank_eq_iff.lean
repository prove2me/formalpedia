-- Prove2me | Theorems.Thm_Geometry_KernelPatterns_rank_eq_iff
-- name    : Geometry.KernelPatterns.rank_eq_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:20:22.355362+00:00
-- url     : https://prove2.me/theorems/6f40879b-c732-4098-ae33-45624c0a5e85
-- title:
--   The rank function records the kernel.
-- statement:
--   The rank function records the kernel.
--
--   ```lean
--   theorem Geometry.KernelPatterns.rank_eq_iff{v : Fin n → X} {i j : Fin n} : rank v i = rank v j ↔ v i = v j := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/KernelPatterns/Faces.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/KernelPatterns/Faces.lean#L72

-- Thm stub generated from Geometry/KernelPatterns/Faces.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Chambers
import Definitions.Def_Geometry_KernelPatterns_Faces

/-!
# Cycle 2: ordered patterns and the faces of the braid arrangement

A kernel pattern remembers which coordinates of a tuple agree; an *ordered*
pattern also remembers how the resulting blocks are ordered.  Geometrically,
kernel patterns index the flats of the braid arrangement while ordered patterns
index its **faces** (relatively open cones): the face containing `v` is cut out
by the full system of comparisons `v i ≤ v j`.

* `rank v i` — the number of blocks of `v` whose value is `< v i`; this is the
  canonical form of an ordered pattern.
* `rank_lt_iff`, `rank_eq_iff` — `rank` records the weak order faithfully.
* `rank_congr`, `rank_comp_strictMono` — ordered patterns are invariant under
  strictly monotone reparametrisation of the values, i.e. they are the
  invariants of the action of the order-automorphisms of the value line.
* `face_eq_iff` — two tuples span the same face iff they have the same ordered
  pattern; `face_convex`; a chamber is the face of an injective tuple
  (`face_eq_chamber`).
* `card_ordPatterns_le_four` — the face counts `1, 1, 3, 13, 75`, the
  ordered Bell (Fubini) numbers OEIS A000670.
-/

open Geometry.KernelPatterns

open Finset

variable {n : ℕ} {X : Type*} [LinearOrder X]

/-! ### The ordered pattern (rank function) -/

theorem Geometry.KernelPatterns.rank_eq_iff{v : Fin n → X} {i j : Fin n} : rank v i = rank v j ↔ v i = v j := by sorry
