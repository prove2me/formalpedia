-- Prove2me | Definitions.Def_Novelty_EmergentGeometryNonUniqueness
-- name    : Novelty_EmergentGeometryNonUniqueness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:22:06.576187+00:00
-- url     : https://prove2.me/theorems/531c9e5f-08db-4beb-b80b-e0a41c559366
-- title:
--   Aether Catalog definitions — Novelty_EmergentGeometryNonUniqueness
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.EmergentGeometryNonUniqueness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/EmergentGeometryNonUniqueness.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EmergentGeometryEntropyCone

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

namespace EmergentGeometry

open Finset

/-! ## A general one-bulk-cell reduction -/

variable {V : Type*} [Fintype V] [DecidableEq V]


/-! ## The two competing three-boundary geometries -/

/-- Cells `0,1,2` are boundary cells, cell `3` is hidden. -/
def threeBdry : Region (Fin 4) := fun v => decide (v ≠ 3)

/-- A hidden bulk cell joined to each boundary cell by a throat of area `1`. -/
def starModel : HoloModel (Fin 4) where
  weight := fun i j => if i = j then 0 else if i = 3 ∨ j = 3 then 1 else 0
  weight_symm := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff]
  weight_nonneg := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff]
  bdry := threeBdry

/-- No hidden cell: the three boundary cells pairwise joined by area `1/2`. -/
def triangleModel : HoloModel (Fin 4) where
  weight := fun i j => if i = j then 0 else if i = 3 ∨ j = 3 then 0 else 1/2
  weight_symm := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff]
  weight_nonneg := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff]
  bdry := threeBdry




/-! ## The two geometries are genuinely different -/




/-! ## Entanglement without an edge: a genuine bridge through the bulk -/





end EmergentGeometry


