-- Prove2me | Definitions.Def_Novelty_EmergentGeometryReconstruction
-- name    : Novelty_EmergentGeometryReconstruction
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:21:04.134865+00:00
-- url     : https://prove2.me/theorems/b3930d85-ecbb-4ac2-b03b-a2fed409f7f0
-- title:
--   Aether Catalog definitions — Novelty_EmergentGeometryReconstruction
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.EmergentGeometryReconstruction`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/EmergentGeometryReconstruction.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EmergentGeometryEntropyCone

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

namespace EmergentGeometry

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Cut areas ignore the diagonal -/



/-! ## The emergent topology is reconstructed too -/




/-! ## Sharpness: the diagonal is pure gauge -/

/-- Re-weighting the self-loops of a geometry. -/
def reDiag (G : BulkGraph V) (d : V → ℝ) (hd : ∀ u, 0 ≤ d u) : BulkGraph V where
  weight u v := if u = v then d u else G.weight u v
  weight_symm u v := by
    rcases eq_or_ne u v with rfl | huv
    · simp
    · simp [huv, Ne.symm huv, G.weight_symm u v]
  weight_nonneg u v := by
    rcases eq_or_ne u v with rfl | huv
    · simpa using hd u
    · simpa [huv] using G.weight_nonneg u v



end EmergentGeometry


