-- Prove2me | solution 1 for EmergentGeometry.entangled_iff_concurrence_pos
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:53:42.229447+00:00
-- url     : https://prove2.me/submissions/13e2d280-1dbc-48bc-ace4-943730aad33f

-- Sol generated from Novelty/EREPRBridge.lean
import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EREqualsEPR
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Theorems.Thm_EmergentGeometry_concurrence_nonneg
import Theorems.Thm_EmergentGeometry_isProduct_of_det_eq_zero
import Theorems.Thm_EmergentSpacetime_product_entanglementDet_zero

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









/-! ## Bulk connectivity: Einstein–Rosen bridges -/






/-! ## The single-throat geometry of a qubit pair -/





/-! ## Two-qubit states: entanglement is a bridge -/

open EmergentSpacetime







open EmergentGeometry in
theorem solution(ψ : TwoQubitState) :
    ¬ IsProduct ψ ↔ 0 < concurrence ψ := by
  constructor
  · intro hnp
    rcases lt_or_eq_of_le (concurrence_nonneg ψ) with h | h
    · exact h
    · exact absurd (isProduct_of_det_eq_zero (by
        have : |entanglementDet ψ| = 0 := by
          simp only [concurrence] at h; linarith
        simpa [entanglementDet, abs_eq_zero] using this)) hnp
  · intro hpos hp
    have := product_entanglementDet_zero hp
    simp [concurrence, this] at hpos
