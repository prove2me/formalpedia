-- Prove2me | Theorems.Thm_BruhatTits_cons_isChain_of
-- name    : BruhatTits.cons_isChain_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:10:12.504367+00:00
-- url     : https://prove2.me/theorems/5ccfa93f-83bb-44e7-b268-81ee01d7b176
-- title:
--   Bruhat Tits: cons is Chain of
-- statement:
--   The Bruhat Tits construction uses the cons is Chain of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L233-L238
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L233-L238

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

theorem BruhatTits.cons_isChain_of {l : List (BruhatTits.Lattice R)} {M L : BruhatTits.Lattice R} (hl : (L :: l).IsBruhatTitsChain)
    (hML : IsStandardNeighbour M L) : (M :: L :: l).IsBruhatTitsChain := by sorry
