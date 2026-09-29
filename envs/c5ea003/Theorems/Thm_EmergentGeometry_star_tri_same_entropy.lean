-- Prove2me | Theorems.Thm_EmergentGeometry_star_tri_same_entropy
-- name    : EmergentGeometry.star_tri_same_entropy
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:41:54.592204+00:00
-- url     : https://prove2.me/theorems/669443be-4482-4f2a-9a99-1330d056055d
-- title:
--   Every boundary region of the two models has the same entropy: the two
-- statement:
--   Every boundary region of the two models has the same entropy: the two
--   geometries are entanglement-indistinguishable.
--
--   ```lean
--   theorem EmergentGeometry.star_tri_same_entropy(A : Region (Fin 4)) (hA : A 3 = false) :
--       entropy starModel A = entropy triangleModel A := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/EmergentGeometryNonUniqueness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/EmergentGeometryNonUniqueness.lean#L98

-- Thm stub generated from Novelty/EmergentGeometryNonUniqueness.lean
import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Definitions.Def_Novelty_EmergentGeometryNonUniqueness

/-!
# The boundary of bulk reconstruction: entropies do not determine the geometry

`Novelty.EREPRBridge` proves that when *every* cell is a boundary cell the
emergent geometry is completely reconstructed from two-point mutual
informations, `w(u,v) = I(u:v)/2`.  This file shows that this reconstruction
theorem is *sharp*: as soon as one hidden bulk cell is allowed, the boundary
entanglement data no longer determines the bulk geometry.

Two explicit three-boundary geometries are compared:

* `starModel`     — a hidden bulk cell joined to each of the three boundary
  cells by a throat of area `1` (a "bulk vertex", the discrete analogue of a
  three-boundary wormhole);
* `triangleModel` — no hidden cell at all, the three boundary cells pairwise
  joined by throats of area `1/2`.

They have *identical* entanglement entropies for every boundary region
(`star_tri_same_entropy`), yet different geometries: in the star the boundary
cells are pairwise non-adjacent (`starModel_no_direct_edge`) while in the
triangle they are.  Consequently the reconstruction map from entanglement to
geometry is not injective in the presence of bulk cells
(`bulk_geometry_not_determined_by_entanglement`), although — by
`bridge_of_mutualInfo_pos` — *connectivity* is still forced: in the star model
the positive mutual information of two boundary cells is carried by a genuine
two-step Einstein–Rosen bridge through the hidden cell
(`starModel_bridge_through_bulk`).
-/

noncomputable section

open EmergentGeometry

open Finset

/-! ## A general one-bulk-cell reduction -/

variable {V : Type*} [Fintype V] [DecidableEq V]


/-! ## The two competing three-boundary geometries -/

theorem EmergentGeometry.star_tri_same_entropy(A : Region (Fin 4)) (hA : A 3 = false) :
    entropy starModel A = entropy triangleModel A := by sorry
