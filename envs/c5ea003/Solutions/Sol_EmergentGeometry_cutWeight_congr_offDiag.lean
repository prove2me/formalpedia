-- Prove2me | solution 1 for EmergentGeometry.cutWeight_congr_offDiag
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:51:48.116386+00:00
-- url     : https://prove2.me/submissions/f364f539-e0a4-4e78-aa39-7487c8ca1b65

-- Sol generated from Novelty/EmergentGeometryReconstruction.lean
import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Definitions.Def_Novelty_EmergentGeometryReconstruction
import Theorems.Thm_EmergentGeometry_sepBit_self

/-!
# Spacetime from entanglement: the full reconstruction theorem

`Novelty.EREPRBridge` reconstructs the *metric data* of a bulk geometry without
hidden cells from two-point entanglement, `w(u,v) = I(u:v)/2`
(`weight_eq_half_mutualInfo`, `bulk_weights_determined_by_mutualInfo`).  That is
a statement about edges.  Here the reconstruction is completed at the level of
the whole geometry:

* `cutWeight_congr_offDiag` — cut areas never see the diagonal of the weight
  matrix, so two geometries agreeing off the diagonal are indistinguishable;
* `entropy_eq_iff_mutualInfo_eq` — for models without hidden bulk cells, the
  *entire* entropy function of every boundary region is determined by, and
  determines, the family of two-point mutual informations.  This is the precise
  sense in which "spacetime emerges from entanglement": a single `V × V` table
  of pairwise entanglements fixes all `2^{|V|}` Ryu–Takayanagi areas;
* `bulkPath_congr_of_mutualInfo` — the *topology* of the emergent spacetime, the
  Einstein–Rosen connectivity relation `BulkPath`, is likewise fixed by the
  two-point data (self-loops, which entanglement cannot see, are also
  irrelevant to connectivity);
* `spacetime_from_entanglement` — the two statements packaged together.

Note that the diagonal weights `w(u,u)` are *not* determined: they are pure
gauge, invisible both to areas and to connectivity.  `weight_diag_is_gauge`
makes this precise, so the reconstruction theorem is sharp.
-/

noncomputable section

open EmergentGeometry

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Cut areas ignore the diagonal -/



/-! ## The emergent topology is reconstructed too -/




/-! ## Sharpness: the diagonal is pure gauge -/





open EmergentGeometry in
omit [DecidableEq V] in
theorem solution(G H : BulkGraph V)
    (h : ∀ u v : V, u ≠ v → G.weight u v = H.weight u v) (f : Region V) :
    cutWeight G f = cutWeight H f := by
  simp only [cutWeight]
  congr 1
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rcases eq_or_ne u v with rfl | huv
  · simp
  · rw [h u v huv]
