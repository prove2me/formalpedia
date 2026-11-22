-- Prove2me | Definitions.Def_Kourovka_Halfspaces_SchreierPaths
-- name    : Kourovka_Halfspaces_SchreierPaths
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:20:04.599956+00:00
-- url     : https://prove2.me/theorems/86354619-b3d5-4901-9a88-ce2007dfd149
-- title:
--   Schreier Paths
-- statement:
--   Definitions and structural lemmas for Schreier Paths, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/SchreierPaths.lean

import Definitions.Def_Kourovka_Halfspaces_SchreierKernel
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry
open Kourovka.Schreier
open Kourovka.Schreier.Transversal
variable {X : Type*}
abbrev step (θ : FreeGroup X →* Multiplicative ℝ) : X × Bool → ℝ :=
  letterHeight fun x => value θ (FreeGroup.of x)
def generatorWord [DecidableEq X] {L : Subgroup (FreeGroup X)}
    (S : Transversal L) (z : S.Edge) :
    List (X × Bool) :=
  z.1.val.toWord ++ [(z.2, true)] ++
    FreeGroup.invRev (S.rep (z.1.val * FreeGroup.of z.2)).toWord
end Kourovka.MetabelianEnumeration.SchreierHeights


