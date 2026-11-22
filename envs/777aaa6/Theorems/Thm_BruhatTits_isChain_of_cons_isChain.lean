-- Prove2me | Theorems.Thm_BruhatTits_isChain_of_cons_isChain
-- name    : BruhatTits.isChain_of_cons_isChain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:10:25.183795+00:00
-- url     : https://prove2.me/theorems/1d4bfcac-2bcf-4881-8f64-62f742447669
-- title:
--   Bruhat Tits: is Chain of cons is Chain
-- statement:
--   The Bruhat Tits construction uses the is Chain of cons is Chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L240-L245
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L240-L245

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

theorem BruhatTits.isChain_of_cons_isChain {l : List (BruhatTits.Lattice R)} {M : BruhatTits.Lattice R} (hl : l ≠ [])
    (h : (M :: l).IsBruhatTitsChain) : l.IsBruhatTitsChain := by sorry
