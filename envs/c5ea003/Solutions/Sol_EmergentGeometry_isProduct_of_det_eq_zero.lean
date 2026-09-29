-- Prove2me | solution 1 for EmergentGeometry.isProduct_of_det_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:51:51.896994+00:00
-- url     : https://prove2.me/submissions/7d68337b-59ef-424d-a4c8-54d70dfb47bf

-- Sol generated from Novelty/EREPRBridge.lean
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









/-! ## Bulk connectivity: Einstein–Rosen bridges -/






/-! ## The single-throat geometry of a qubit pair -/





/-! ## Two-qubit states: entanglement is a bridge -/

open EmergentSpacetime







open EmergentGeometry in
theorem solution{ψ : TwoQubitState} (h : Matrix.det ψ = 0) :
    IsProduct ψ := by
  rw [Matrix.det_fin_two] at h
  by_cases h00 : ψ 0 0 = 0
  · by_cases h01 : ψ 0 1 = 0
    · exact ⟨![0, 1], ![ψ 1 0, ψ 1 1], by
        intro i j; fin_cases i <;> fin_cases j <;> simp [h00, h01]⟩
    · have h10 : ψ 1 0 = 0 := by
        rw [h00] at h
        have hz : ψ 0 1 * ψ 1 0 = 0 := by linarith
        rcases mul_eq_zero.1 hz with h' | h'
        · exact absurd h' h01
        · exact h'
      exact ⟨![ψ 0 1, ψ 1 1], ![0, 1], by
        intro i j; fin_cases i <;> fin_cases j <;> simp [h00, h10]⟩
  · refine ⟨![1, ψ 1 0 / ψ 0 0], ![ψ 0 0, ψ 0 1], ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;> simp [h00]
    all_goals (field_simp; nlinarith [h])
