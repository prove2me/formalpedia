-- Prove2me | Theorems.Thm_List_smul_lattice_def
-- name    : List.smul_lattice_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:11:24.042115+00:00
-- url     : https://prove2.me/theorems/cc21d5fa-a438-4b82-9ceb-d858479d7a01
-- title:
--   List: smul lattice def
-- statement:
--   The List construction uses the smul lattice def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L279-L281
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L279-L281

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

theorem List.smul_lattice_def (g : GL (Fin 2) K) (l : List (BruhatTits.Lattice R)) :
    g • l = l.map (fun L ↦ g • L) := by sorry
