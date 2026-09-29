-- Prove2me | Theorems.Thm_EmergentGeometry_entropy_single_bulk
-- name    : EmergentGeometry.entropy_single_bulk
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:40:38.507519+00:00
-- url     : https://prove2.me/theorems/d2bee8b5-e657-4b22-a0f3-594dd1393c97
-- title:
--   If exactly one cell `c` is hidden, the min-cut entropy is the minimum of
-- statement:
--   If exactly one cell `c` is hidden, the min-cut entropy is the minimum of
--   the two cut areas obtained by putting `c` inside or outside the region.
--
--   ```lean
--   theorem EmergentGeometry.entropy_single_bulk{M : HoloModel V} {c : V} (hc : M.bdry c = false)
--       (hb : ∀ v, v ≠ c → M.bdry v = true) (A : Region V) :
--       entropy M A = min (cutWeight M.toBulkGraph (Function.update A c false))
--         (cutWeight M.toBulkGraph (Function.update A c true)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/EmergentGeometryNonUniqueness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/EmergentGeometryNonUniqueness.lean#L43

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

theorem EmergentGeometry.entropy_single_bulk{M : HoloModel V} {c : V} (hc : M.bdry c = false)
    (hb : ∀ v, v ≠ c → M.bdry v = true) (A : Region V) :
    entropy M A = min (cutWeight M.toBulkGraph (Function.update A c false))
      (cutWeight M.toBulkGraph (Function.update A c true)) := by sorry
