-- Prove2me | Theorems.Thm_BruhatTits_isSimpleChain_of_cons_isSimpleChain
-- name    : BruhatTits.isSimpleChain_of_cons_isSimpleChain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:10:40.034308+00:00
-- url     : https://prove2.me/theorems/95715ca8-0e13-473a-8e2a-0d8838d9b8e4
-- title:
--   Bruhat Tits: is Simple Chain of cons is Simple Chain
-- statement:
--   The Bruhat Tits construction uses the is Simple Chain of cons is Simple Chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L257-L268
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L257-L268

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

theorem BruhatTits.isSimpleChain_of_cons_isSimpleChain {l : List (BruhatTits.Lattice R)} {M : BruhatTits.Lattice R}
    (hl : l ≠ [])
    (h : (M :: l).IsSimpleChain) : l.IsSimpleChain := by sorry
