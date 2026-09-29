-- Prove2me | Definitions.Def_mme_dwz_fourth_public_ordinary_181_reduction_data
-- name    : mme_dwz_fourth_public_ordinary_181_reduction_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T05:11:44.308115+00:00
-- url     : https://prove2.me/theorems/e6c1bc3e-80b3-4ecd-a63f-e72d70dd4f49
-- title:
--   Reducing the fourth-power value to ordinary six-region endpoints
-- statement:
--   Definitions used by the statement of mme_dwz_fourth_public_ordinary_181_reduction, from the exact fourth-power scalar assembly.
-- source:
--   Formalization of the exact rational scalar certificate and the tensor assembly of the Duan-Wu-Zhou fourth-power construction. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 .

import Definitions.Def_mme_dwz_fourth_six_value_final_node_split_data
import Theorems.Thm_mme_dwz_fourth_six_value_final_node_split
import Definitions.Def_mme_dwz_fourth_public_component_coverage_data
import Theorems.Thm_mme_dwz_fourth_public_component_coverage
import Definitions.Def_mme_dwz_fourth_prescribedZ_181_integration_data
import Theorems.Thm_mme_dwz_fourth_prescribedZ_181_integration

open MME
open MME.DWZFourthTensorLedger
open MME.DWZFourthSixFinalSplit
open scoped Classical

universe u

set_option autoImplicit false

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

namespace MME.DWZFourthPublicOrdinary181

/-- Endpoint facts for exactly the 21 positive fourth-power blocks. -/
def PositiveFourthSixEndpoints
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ) : Prop :=
  ∀ index : Fin 180,
    publicCoverageTier (componentSpecAt index) =
        PublicCoverageTier.fourthPositivePrescribedZOpen →
      HasSixSymmetricTauValueAtLeast
        (tensorAt (properLedgerIndex index)) tau
        (Real.exp (properLedgerRate index : ℝ))

/-- The complementary 159 endpoint facts: six atomic blocks, all 129 square
rows, and the 24 fourth-boundary rows.  Each of these lies in a public
exact-MM, 022, or cyclic-112 endpoint class; this definition exposes their
remaining theorem-to-ledger normalization in one place. -/
def PublicComplementSixEndpoints
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ) : Prop :=
  ∀ index : Fin 180,
    publicCoverageTier (componentSpecAt index) ≠
        PublicCoverageTier.fourthPositivePrescribedZOpen →
      HasSixSymmetricTauValueAtLeast
        (tensorAt (properLedgerIndex index)) tau
        (Real.exp (properLedgerRate index : ℝ))

end MME.DWZFourthPublicOrdinary181


