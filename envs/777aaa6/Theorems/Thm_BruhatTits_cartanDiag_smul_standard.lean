-- Prove2me | Theorems.Thm_BruhatTits_cartanDiag_smul_standard
-- name    : BruhatTits.cartanDiag_smul_standard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:22:17.100805+00:00
-- url     : https://prove2.me/theorems/1d25efc3-a1f6-4f68-9990-2fb8da5def03
-- title:
--   Bruhat Tits: cartan Diag smul standard
-- statement:
--   The Bruhat Tits construction uses the cartan Diag smul standard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L128-L138
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L128-L138

import Definitions.Def_BruhatTits_Graph_Graph
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Graph_GroupAction
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
open BruhatTits
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
omit [IsDiscreteValuationRing ↥R] [IsFractionRing (↥R) K]

theorem BruhatTits.cartanDiag_smul_standard
    (ϖ : R) (hϖ : Irreducible ϖ) (f : Fin 2 → ℤ) :
    cartanDiag ϖ hϖ f • Lattice.standard R =
      (Basis.twist (Pi.basisFun K (Fin 2)) hϖ f).toLattice := by sorry
