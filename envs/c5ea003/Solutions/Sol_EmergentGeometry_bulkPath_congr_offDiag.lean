-- Prove2me | solution 1 for EmergentGeometry.bulkPath_congr_offDiag
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:45:57.378318+00:00
-- url     : https://prove2.me/submissions/393bc352-fa55-4332-aad8-68968906cd24

-- Sol generated from Novelty/EmergentGeometryReconstruction.lean
import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Definitions.Def_Novelty_EmergentGeometryReconstruction

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
    (h : ∀ u v : V, u ≠ v → G.weight u v = H.weight u v) (u v : V) :
    BulkPath G u v ↔ BulkPath H u v := by
  have key : ∀ (G H : BulkGraph V), (∀ u v : V, u ≠ v → G.weight u v = H.weight u v) →
      ∀ u v : V, BulkPath G u v → BulkPath H u v := by
    intro G H h u v hp
    induction hp with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
        rename_i b c _
        rcases eq_or_ne b c with rfl | hbc'
        · exact ih
        · exact ih.tail (by simpa only [BulkAdj, ← h b c hbc'] using hbc)
  exact ⟨key G H h u v, key H G (fun a b hab => (h a b hab).symm) u v⟩
