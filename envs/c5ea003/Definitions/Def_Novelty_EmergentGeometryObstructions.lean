-- Prove2me | Definitions.Def_Novelty_EmergentGeometryObstructions
-- name    : Novelty_EmergentGeometryObstructions
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:21:50.768206+00:00
-- url     : https://prove2.me/theorems/92b5a39b-2e6d-4994-85d7-8e14f59d0315
-- title:
--   Aether Catalog definitions — Novelty_EmergentGeometryObstructions
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.EmergentGeometryObstructions`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/EmergentGeometryObstructions.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EmergentGeometryEntropyCone

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

namespace EmergentGeometry

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## A state with no geometric dual -/



/-! ### The obstruction is genuinely new: monogamy is strictly stronger than the
general quantum entropy inequalities -/

/-- The four-party GHZ entropy pattern on three parties: every nonempty
marginal has entropy `1`. -/
def ghzVector (s : Finset (Fin 3)) : ℚ := if s = ∅ then 0 else 1




/-! ## Stability of the emergent geometry -/

/-- Total area discrepancy between two bulk geometries. -/
def geometryDist (G G' : BulkGraph V) : ℝ :=
  (∑ u, ∑ v, |G.weight u v - G'.weight u v|) / 2




/-! ## The Einstein–Rosen network is the EPR network -/

/-- Two boundary cells are *directly entangled* when their mutual information is
positive. -/
def EntangledPair (M : HoloModel V) (u v : V) : Prop :=
  0 < mutualInfo M (single u) (single v)


end EmergentGeometry


