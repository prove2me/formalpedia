-- Prove2me | Theorems.Thm_BruhatTits_mem_stabilizer_twist_iff_mem
-- name    : BruhatTits.mem_stabilizer_twist_iff_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:22:43.579082+00:00
-- url     : https://prove2.me/theorems/3dbaa333-7183-410f-8663-b85701c3ec59
-- title:
--   Bruhat Tits: mem stabilizer twist iff mem
-- statement:
--   The Bruhat Tits construction uses the mem stabilizer twist iff mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L279-L323
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L279-L323

import Definitions.Def_BruhatTits_Graph_Graph
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Graph_GroupAction
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
open BruhatTits
variable [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem BruhatTits.mem_stabilizer_twist_iff_mem {ϖ : R} (hϖ : Irreducible ϖ) (g : GL (Fin 2) R)
    (f : Fin 2 → ℤ) :
    (g : GL (Fin 2) K) ∈ MulAction.stabilizer (GL (Fin 2) K)
      ((Basis.twist (Pi.basisFun K (Fin 2)) hϖ f).toLattice (R := R)) ↔
    ϖ.val ^ (f 1 - f 0) * g 0 1 ∈ R ∧
      ϖ.val ^ (f 0 - f 1) * g 1 0 ∈ R := by sorry
