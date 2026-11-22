-- Prove2me | Theorems.Thm_BruhatTits_singleton_isSimpleChain
-- name    : BruhatTits.singleton_isSimpleChain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:11:32.900173+00:00
-- url     : https://prove2.me/theorems/d4e5d51a-de8a-44d9-9b47-54bd3dc51b30
-- title:
--   Bruhat Tits: singleton is Simple Chain
-- statement:
--   The Bruhat Tits construction uses the singleton is Simple Chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L253-L255
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L253-L255

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

theorem BruhatTits.singleton_isSimpleChain (L : BruhatTits.Lattice R) : [L].IsSimpleChain := by sorry
