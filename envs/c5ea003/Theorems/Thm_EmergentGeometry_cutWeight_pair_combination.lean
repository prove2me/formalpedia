-- Prove2me | Theorems.Thm_EmergentGeometry_cutWeight_pair_combination
-- name    : EmergentGeometry.cutWeight_pair_combination
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:35:34.054869+00:00
-- url     : https://prove2.me/theorems/156016d2-73a2-43f9-89dc-e64c75d71b90
-- title:
--   The two-point cut combination of a weighted graph isolates a single edge:
-- statement:
--   The two-point cut combination of a weighted graph isolates a single edge:
--   `cut({u}) + cut({v}) - cut({u,v}) = 2 w(u,v)`.
--
--   ```lean
--   theorem EmergentGeometry.cutWeight_pair_combination(G : BulkGraph V) {u v : V} (huv : u ≠ v) :
--       cutWeight G (single u) + cutWeight G (single v)
--           - cutWeight G (fun x => single u x || single v x)
--         = 2 * G.weight u v := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/EREPRBridge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/EREPRBridge.lean#L60

-- Thm stub generated from Novelty/EREPRBridge.lean
import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EREqualsEPR
import Definitions.Def_Novelty_EmergentGeometryEntropyCone

/-!
# ER = EPR: bulk bridges are exactly boundary entanglement

Building on `Novelty.EmergentGeometryEntropyCone` (min-cut / Ryu–Takayanagi
entropies of a finite bulk geometry) and on `Novelty.EREqualsEPR` (the two-qubit
toy model), this file proves the two halves of the ER=EPR correspondence in the
toy setting:

* **Geometry from entanglement** (`weight_eq_half_mutualInfo`,
  `bulk_weights_determined_by_mutualInfo`): in a model without hidden bulk cells
  every edge weight — i.e. the entire bulk metric — is recovered from
  two-point mutual informations, `w(u,v) = I(u:v)/2`.
* **Entanglement forces a bridge** (`mutualInfo_eq_zero_of_no_bridge`,
  `bridge_of_mutualInfo_pos`): two boundary regions with positive mutual
  information *must* be joined by a positive-weight bulk path, an
  Einstein–Rosen bridge; conversely disconnected regions are unentangled
  (their entropies are exactly additive).
* **EPR ⟺ ER for a qubit pair** (`ER_EPR_correspondence`): a real two-qubit
  pure state is entangled if and only if the associated one-throat geometry,
  whose throat weight is the concurrence, contains a bulk bridge between the
  two boundary qubits.
-/

noncomputable section

open EmergentGeometry

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Boundary regions consisting of one or two cells -/

theorem EmergentGeometry.cutWeight_pair_combination(G : BulkGraph V) {u v : V} (huv : u ≠ v) :
    cutWeight G (single u) + cutWeight G (single v)
        - cutWeight G (fun x => single u x || single v x)
      = 2 * G.weight u v := by sorry
