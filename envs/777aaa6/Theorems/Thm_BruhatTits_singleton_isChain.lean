-- Prove2me | Theorems.Thm_BruhatTits_singleton_isChain
-- name    : BruhatTits.singleton_isChain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:10:09.540184+00:00
-- url     : https://prove2.me/theorems/d6456226-4984-41e3-9ced-b02e05ce6a20
-- title:
--   Bruhat Tits: singleton is Chain
-- statement:
--   The Bruhat Tits construction uses the singleton is Chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L229-L231
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L229-L231

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

theorem BruhatTits.singleton_isChain (L : BruhatTits.Lattice R) : [L].IsBruhatTitsChain := by sorry
