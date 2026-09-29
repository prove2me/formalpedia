-- Prove2me | Theorems.Thm_mme_CW_fourth_Yzero_exact_Z_basis_router
-- name    : mme_CW_fourth_Yzero_exact_Z_basis_router
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-21T19:00:28.226097+00:00
-- url     : https://prove2.me/theorems/71cf6a27-5264-45b3-9110-f9abbca09c56
-- title:
--   Exact canonical Z-basis router for every Y-zero fourth CW boundary block
-- statement:
--   For every q and j+k=8, the literal Y-zero fourth constituent T_(j,0,k) maps to the matrix tensor <D,1,1>, preserving all canonical Z coordinates as distinct standard matrix coordinates. Here D is the full cardinality of the canonical grade-k Z alphabet.
-- source:
--   Fourth-power CW boundary tensor expansion, refining the accepted literal boundary-code restriction to preserve the canonical Z basis. Used for DWZ prescribed-Z value endpoints.

import Definitions.Def_mme_complete_split_cw_fourth_labels
import Definitions.Def_mme_tensor_bridge
open MME MME.StothersFourth MME.CompleteSplit.CWFourth
universe u
set_option autoImplicit false

theorem mme_CW_fourth_Yzero_exact_Z_basis_router
    (K : Type u) [Field K] (q : ℕ) (j k : Fin 9) (hjk : j.val + k.val = 8) :
    ∃ coord : LiftedCoarseCoordinate.{u} q k ↪
        Fin (Fintype.card (LiftedCoarseCoordinate.{u} q k)),
      ∃ maps : ∀ s, (cwFourthConstituent K q j 0 k).V s →ₗ[K]
        (MMObj K (Fintype.card (LiftedCoarseCoordinate.{u} q k)) 1 1).V s,
        PiTensorProduct.map maps (cwFourthConstituent K q j 0 k).t =
          (MMObj K (Fintype.card (LiftedCoarseCoordinate.{u} q k)) 1 1).t ∧
        ∀ p, maps 2 (constituentBasis K q j 0 k 2 p) =
          (Pi.single ((0 : Fin 1), coord p) 1 :
            Fin 1 × Fin (Fintype.card (LiftedCoarseCoordinate.{u} q k)) → K)  := by sorry
