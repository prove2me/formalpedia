-- Prove2me | Theorems.Thm_List_smul_lattice_length
-- name    : List.smul_lattice_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:10:13.218221+00:00
-- url     : https://prove2.me/theorems/dc3512ce-fb1d-4772-8837-8b12501bc7b5
-- title:
--   List: smul lattice length
-- statement:
--   The List construction uses the smul lattice length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L284-L286
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L284-L286

import Definitions.Def_BruhatTits_Graph_Vertices
import Definitions.Def_BruhatTits_Lattice_Quotient
import Definitions.Def_BruhatTits_Utils_GLSubmoduleAction
import Definitions.Def_BruhatTits_Utils_List
import Definitions.Def_BruhatTits_Graph_Edges
set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K] {R : Subring K}
open BruhatTits
open Pointwise
open IsLocalRing

theorem List.smul_lattice_length (g : GL (Fin 2) K) (l : List (BruhatTits.Lattice R)) :
    (g • l).length = l.length := by sorry
