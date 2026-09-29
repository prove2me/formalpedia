-- Prove2me | solution 1 for EmergentGeometry.entropy_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:56:18.510907+00:00
-- url     : https://prove2.me/submissions/4c45fe7b-bcab-468b-9987-d708d71b3707

-- Sol generated from Novelty/EmergentGeometryObstructions.lean
import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Definitions.Def_Novelty_EmergentGeometryObstructions
import Theorems.Thm_EmergentGeometry_cutWeight_dist_le
import Theorems.Thm_EmergentGeometry_entropy_le_of_admissible
import Theorems.Thm_EmergentGeometry_exists_minimal_surface

/-!
# Obstructions and stability for emergent geometry

Three complementary results about which quantum states can have a geometric
(bulk) dual, and how robust the emergent geometry is.

* **Obstruction.** `no_geometric_dual_of_ghz_type` shows that the entropy
  pattern in which every one-, two- and three-party marginal of a four-party
  state has entropy `1` — the pattern of the four-party GHZ state — is realised
  by *no* bulk geometry whatsoever.  Entanglement alone does not build
  spacetime: only entanglement obeying monogamy does.

* **Stability.** `entropy_lipschitz` shows that the entanglement entropies
  depend Lipschitz-continuously on the bulk geometry: perturbing all areas by a
  total of `ε` perturbs every entropy by at most `ε/2`.  Emergent geometry is
  therefore not an artefact of fine tuning.

* **Identification of the two connectivity notions.**
  `bulkPath_iff_entanglementPath` shows that, in a model without hidden cells,
  the bulk connectivity relation is *exactly* the transitive closure of pairwise
  entanglement: the Einstein–Rosen network and the EPR network coincide as
  graphs.
-/

noncomputable section

open EmergentGeometry

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## A state with no geometric dual -/



/-! ### The obstruction is genuinely new: monogamy is strictly stronger than the
general quantum entropy inequalities -/





/-! ## Stability of the emergent geometry -/





/-! ## The Einstein–Rosen network is the EPR network -/




open EmergentGeometry in
theorem solution(M M' : HoloModel V) (hb : M.bdry = M'.bdry)
    (A : Region V) :
    |entropy M A - entropy M' A| ≤ geometryDist M.toBulkGraph M'.toBulkGraph := by
  have hadm : ∀ f, Admissible M A f ↔ Admissible M' A f := by
    intro f
    constructor <;> intro h v hv
    · exact h v (by rw [hb]; exact hv)
    · exact h v (by rw [← hb]; exact hv)
  obtain ⟨f, hf, hval⟩ := exists_minimal_surface M A
  obtain ⟨g, hg, hval'⟩ := exists_minimal_surface M' A
  have h1 : entropy M A ≤ cutWeight M.toBulkGraph g :=
    entropy_le_of_admissible ((hadm g).2 hg)
  have h2 : entropy M' A ≤ cutWeight M'.toBulkGraph f :=
    entropy_le_of_admissible ((hadm f).1 hf)
  have b1 := cutWeight_dist_le M.toBulkGraph M'.toBulkGraph f
  have b2 := cutWeight_dist_le M.toBulkGraph M'.toBulkGraph g
  rw [abs_le] at b1 b2 ⊢
  exact ⟨by rw [hval] at *; linarith [b1.1, h2, hval], by
    rw [hval'] at *; linarith [b2.2, h1, hval']⟩
