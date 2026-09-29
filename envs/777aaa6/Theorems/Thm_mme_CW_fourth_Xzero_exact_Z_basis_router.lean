-- Prove2me | Theorems.Thm_mme_CW_fourth_Xzero_exact_Z_basis_router
-- name    : mme_CW_fourth_Xzero_exact_Z_basis_router
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-21T18:41:57.981517+00:00
-- url     : https://prove2.me/theorems/688b37b6-9806-4a13-aef0-5e8e7e69534f
-- title:
--   Exact canonical Z-basis router for every X-zero fourth CW boundary block
-- statement:
--   For every CW parameter q and boundary address (0,j,k) with j+k=8, there are explicit modewise linear maps to the matrix tensor <1,1,D>, where D is the full number of canonical grade-k fourth coordinates. The maps preserve each canonical Z basis coordinate as a distinct standard matrix coordinate, so arbitrary prescribed Z-word projections can be transported through tensor powers.
-- source:
--   Fourth-power CW boundary tensor expansion, refining the accepted literal boundary-code restriction to preserve the canonical Z basis. Used for DWZ prescribed-Z value endpoints.

import Definitions.Def_mme_complete_split_cw_fourth_labels
import Definitions.Def_mme_tensor_bridge
open MME MME.StothersFourth MME.CompleteSplit.CWFourth
universe u
set_option autoImplicit false

theorem mme_CW_fourth_Xzero_exact_Z_basis_router
    (K : Type u) [Field K] (q : ℕ) (j k : Fin 9) (hjk : j.val + k.val = 8) :
    ∃ coord : LiftedCoarseCoordinate.{u} q k ↪
        Fin (Fintype.card (LiftedCoarseCoordinate.{u} q k)),
      ∃ maps : ∀ s, (cwFourthConstituent K q 0 j k).V s →ₗ[K]
        (MMObj K 1 1 (Fintype.card (LiftedCoarseCoordinate.{u} q k))).V s,
        PiTensorProduct.map maps (cwFourthConstituent K q 0 j k).t =
          (MMObj K 1 1 (Fintype.card (LiftedCoarseCoordinate.{u} q k))).t ∧
        ∀ p, maps 2 (constituentBasis K q 0 j k 2 p) =
          (Pi.single (coord p, (0 : Fin 1)) 1 :
            Fin (Fintype.card (LiftedCoarseCoordinate.{u} q k)) × Fin 1 → K)  := by sorry
