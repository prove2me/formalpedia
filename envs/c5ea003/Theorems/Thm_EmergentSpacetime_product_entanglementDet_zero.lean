-- Prove2me | Theorems.Thm_EmergentSpacetime_product_entanglementDet_zero
-- name    : EmergentSpacetime.product_entanglementDet_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:39:27.395484+00:00
-- url     : https://prove2.me/theorems/e0a55cfe-47a9-4409-ac53-4964914912c9
-- title:
--   Product states have zero entanglement determinant.
-- statement:
--   Product states have zero entanglement determinant.
--
--   ```lean
--   theorem EmergentSpacetime.product_entanglementDet_zero{ψ : TwoQubitState} (h : IsProduct ψ) :
--       entanglementDet ψ = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/EREqualsEPR.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/EREqualsEPR.lean#L94

-- Thm stub generated from Novelty/EREqualsEPR.lean
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

theorem EmergentSpacetime.product_entanglementDet_zero{ψ : TwoQubitState} (h : IsProduct ψ) :
    entanglementDet ψ = 0 := by sorry
