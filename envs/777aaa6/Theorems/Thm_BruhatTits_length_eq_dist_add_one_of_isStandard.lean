-- Prove2me | Theorems.Thm_BruhatTits_length_eq_dist_add_one_of_isStandard
-- name    : BruhatTits.length_eq_dist_add_one_of_isStandard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:11:17.112079+00:00
-- url     : https://prove2.me/theorems/8498e23c-685a-4739-b711-908fd52430f3
-- title:
--   Bruhat Tits: length eq dist add one of is Standard
-- statement:
--   If `L₀, ..., Lₙ` is a standard chain of length `n + 1`, `dist L₀ Lₙ = n`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L335-L360
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L335-L360

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
set_option synthInstance.maxHeartbeats 30000
variable [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem BruhatTits.length_eq_dist_add_one_of_isStandard {l : List (BruhatTits.Lattice R)} (hl : l.IsStandard) :
    l.length = dist (l.head hl.ne_nil) (l.getLast hl.ne_nil) + 1 := by sorry
