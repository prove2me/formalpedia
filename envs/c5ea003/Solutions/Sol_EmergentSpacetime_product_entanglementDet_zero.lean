-- Prove2me | solution 1 for EmergentSpacetime.product_entanglementDet_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:51:52.405714+00:00
-- url     : https://prove2.me/submissions/785aadef-7173-48e3-8185-52cc300c8884

-- Sol generated from Novelty/EREqualsEPR.lean
import Mathlib
import Definitions.Def_Novelty_EREqualsEPR

/-!
# A finite ER=EPR toy model

This file isolates a mathematically precise finite statement behind the ER=EPR
slogan.  A pure two-qubit state is represented by its real coefficient matrix.
Its one-qubit reduced density matrices are computed by contraction.  The Bell
state has maximally mixed marginals and nonzero determinant, hence cannot be a
product state.

The bulk toy geometry consists of one possible Einstein--Rosen throat.  Its
weight is reconstructed from boundary entanglement entropies by the two-vertex
cut formula.  For the Bell state the reconstructed throat has unit weight.
-/

noncomputable section

open EmergentSpacetime
























open EmergentSpacetime in
theorem solution{ψ : TwoQubitState} (h : IsProduct ψ) :
    entanglementDet ψ = 0 := by
  obtain ⟨u, v, huv⟩ := h
  simp [entanglementDet, Matrix.det_fin_two, huv]
  ring
