-- Prove2me | Theorems.Thm_BruhatTits_stabilizer_fun_mk_eq_sup
-- name    : BruhatTits.stabilizer_fun_mk_eq_sup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:22:27.664375+00:00
-- url     : https://prove2.me/theorems/c100a98e-daac-4172-8ecd-aafbfd54c218
-- title:
--   Bruhat Tits: stabilizer fun mk eq sup
-- statement:
--   The pointwise stabilizer of the `GL₂(K)`-action on a family of vertices `{⟦Lᵢ⟧}ᵢ` is `Kˣ * Stab({Lᵢ})`.
--   We express the stabilizer of `{⟦Lᵢ⟧}ᵢ` as the stabilizer of the function `i ↦ ⟦Lᵢ⟧`. Here `GL₂(K)`
--   acts pointwise on pi types.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L423-L479
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L423-L479

import Definitions.Def_BruhatTits_Graph_Graph
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Graph_GroupAction
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
open BruhatTits
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
open Matrix GeneralLinearGroup

theorem BruhatTits.stabilizer_fun_mk_eq_sup {ι : Type*} (L : ι → BruhatTits.Lattice R) :
    MulAction.stabilizer (GL (Fin 2) K) (fun i ↦ Vertices.mk (L i)) =
      (embDiagonal K (Fin 2)).range ⊔
        MulAction.stabilizer (GL (Fin 2) K) L := by sorry
