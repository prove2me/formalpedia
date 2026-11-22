-- Prove2me | Theorems.Thm_List_IsSimpleChain_exists_GL_forall_smul
-- name    : List.IsSimpleChain.exists_GL_forall_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:11:19.981424+00:00
-- url     : https://prove2.me/theorems/cb287038-98c7-434d-9de0-d3c87fb6d99f
-- title:
--   Is Simple Chain: exists GL forall smul
-- statement:
--   (Implementation detail) Intermediate lemma for `exists_trafo_to_isStandard`, more adapted
--   to induction.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L614-L644
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L614-L644

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
variable [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem List.IsSimpleChain.exists_GL_forall_smul (l : List (BruhatTits.Lattice R))
    (hl : l.IsSimpleChain) :
    ∃ (g : GL (Fin 2) K) (b : Basis (Fin 2) K (Fin 2 → K)) (ϖ : R) (hϖ : Irreducible ϖ),
    l.zipIdx.Forall (fun (L, n) ↦ g • L = (b.ntwist₂ hϖ (l.length - n - 1) 0).toLattice) := by sorry
