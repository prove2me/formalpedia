-- Prove2me | Definitions.Def_Geometry_KernelPatterns_Faces
-- name    : Geometry_KernelPatterns_Faces
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:38:04.969242+00:00
-- url     : https://prove2.me/theorems/49090fc9-8ea6-4dd7-a23d-fbab7788e7fe
-- title:
--   Aether Catalog definitions — Geometry_KernelPatterns_Faces
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.KernelPatterns.Faces`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/KernelPatterns/Faces.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Chambers
import Definitions.Def_Geometry_KernelPatterns_Core

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

namespace Geometry.KernelPatterns

open Finset

variable {n : ℕ} {X : Type*} [LinearOrder X]

/-! ### The ordered pattern (rank function) -/

/-- The rank of the coordinate `i`: the number of blocks of `v` carrying a
value strictly smaller than `v i`. -/
def rank (v : Fin n → X) (i : Fin n) : Fin n :=
  ⟨(univ.filter fun j => pat v j = j ∧ v j < v i).card, by
    have h1 : pat v i ∉ (univ.filter fun j => pat v j = j ∧ v j < v i) := by
      simp [apply_pat]
    have h2 : (univ.filter fun j => pat v j = j ∧ v j < v i) ⊂ univ :=
      ⟨Finset.subset_univ _, fun h => h1 (h (Finset.mem_univ _))⟩
    simpa using Finset.card_lt_card h2⟩








/-! ### Faces of the braid arrangement -/

/-- The face of the braid arrangement spanned by `v`: the tuples inducing the
same weak order. -/
def face (v : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {w | ∀ i j, (v i < v j ↔ w i < w j)}





/-! ### Counting ordered patterns: the Fubini numbers -/

/-- The finset of ordered patterns of length `n`. -/
def ordPatterns (n : ℕ) : Finset (Fin n → Fin n) :=
  univ.image fun v : Fin n → Fin n => rank v









end Geometry.KernelPatterns


