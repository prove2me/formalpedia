-- Prove2me | solution 1 for EmergentGeometry.entropy_single_bulk
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:56:19.626829+00:00
-- url     : https://prove2.me/submissions/74803ea5-65a4-40c5-bfc2-95c7591217bb

-- Sol generated from Novelty/EmergentGeometryNonUniqueness.lean
import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Definitions.Def_Novelty_EmergentGeometryNonUniqueness
import Theorems.Thm_EmergentGeometry_entropy_le_of_admissible
import Theorems.Thm_EmergentGeometry_exists_minimal_surface

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







/-! ## The two geometries are genuinely different -/




/-! ## Entanglement without an edge: a genuine bridge through the bulk -/






open EmergentGeometry in
theorem solution{M : HoloModel V} {c : V} (hc : M.bdry c = false)
    (hb : ∀ v, v ≠ c → M.bdry v = true) (A : Region V) :
    entropy M A = min (cutWeight M.toBulkGraph (Function.update A c false))
      (cutWeight M.toBulkGraph (Function.update A c true)) := by
  have hadm : ∀ b : Bool, Admissible M A (Function.update A c b) := by
    intro b v hv
    have hvc : v ≠ c := by
      intro h; rw [h, hc] at hv; exact Bool.noConfusion hv
    simp [Function.update_of_ne hvc]
  refine le_antisymm ?_ ?_
  · exact le_min (entropy_le_of_admissible (hadm false)) (entropy_le_of_admissible (hadm true))
  · obtain ⟨f, hf, hval⟩ := exists_minimal_surface M A
    have hfeq : f = Function.update A c (f c) := by
      funext v
      by_cases hvc : v = c
      · subst hvc; simp
      · rw [Function.update_of_ne hvc, hf v (hb v hvc)]
    rw [hval, hfeq]
    cases f c with
    | false => exact min_le_left _ _
    | true => exact min_le_right _ _
