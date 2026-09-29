-- Prove2me | solution 1 for EmergentGeometry.bulkPath_iff_entanglementPath
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:49:19.594227+00:00
-- url     : https://prove2.me/submissions/3c3c6bfa-d602-4c27-9caa-0777579767f9

-- Sol generated from Novelty/EmergentGeometryObstructions.lean
import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Definitions.Def_Novelty_EmergentGeometryObstructions
import Theorems.Thm_EmergentGeometry_weight_eq_half_mutualInfo

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
theorem solution{M : HoloModel V} (h : NoBulk M) (u v : V) :
    BulkPath M.toBulkGraph u v ↔ Relation.ReflTransGen (EntangledPair M) u v := by
  have hstep : ∀ x y : V, x ≠ y → (BulkAdj M.toBulkGraph x y ↔ EntangledPair M x y) := by
    intro x y hxy
    rw [BulkAdj, EntangledPair, weight_eq_half_mutualInfo h hxy]
    constructor <;> intro hh <;> linarith
  constructor
  · intro hp
    induction hp with
    | refl => exact Relation.ReflTransGen.refl
    | tail hbefore hlast ih =>
      rename_i b c
      rcases eq_or_ne b c with rfl | hbc
      · exact ih
      · exact ih.tail ((hstep b c hbc).1 hlast)
  · intro hp
    induction hp with
    | refl => exact Relation.ReflTransGen.refl
    | tail hbefore hlast ih =>
      rename_i b c
      rcases eq_or_ne b c with rfl | hbc
      · exact ih
      · exact ih.tail ((hstep b c hbc).2 hlast)
