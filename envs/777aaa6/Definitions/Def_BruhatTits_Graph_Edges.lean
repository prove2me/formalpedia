-- Prove2me | Definitions.Def_BruhatTits_Graph_Edges
-- name    : BruhatTits_Graph_Edges
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T11:09:10.778321+00:00
-- url     : https://prove2.me/theorems/47833e9f-8f8b-4a68-b9dc-65001321fe8b
-- title:
--   Edges
-- statement:
--   Definitions and structural lemmas for Edges, from Judith Ludwig, Christian Merten, and contributors's pinned The Bruhat–Tits tree development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean

import Definitions.Def_BruhatTits_Graph_Vertices
import Definitions.Def_BruhatTits_Lattice_Quotient
import Definitions.Def_BruhatTits_Utils_GLSubmoduleAction
import Definitions.Def_BruhatTits_Utils_List
set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K] {R : Subring K}
namespace BruhatTits
open Pointwise
section IsNeighbour
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
def IsNeighbour (x y : Vertices R) : Prop := inv x y = 1
end IsNeighbour
section StandardNeighbour
structure IsStandardNeighbour (M L : BruhatTits.Lattice R) : Prop where
  lt : M.M < L.M
  ϖlt : ∀ (ϖ : R) (_ : Irreducible ϖ), ϖ • L.M < M.M
variable [IsDiscreteValuationRing R]
variable [IsFractionRing R K]
end StandardNeighbour
open IsLocalRing
section Chain
structure _root_.List.IsBruhatTitsChain (l : List (BruhatTits.Lattice R)) : Prop where
  ne_nil : l ≠ []
  isStandardNeighbour : l.Chain' IsStandardNeighbour
structure _root_.List.IsSimpleChain (l : List (BruhatTits.Lattice R)) : Prop extends List.IsBruhatTitsChain l where
  no_backtrack :
    (List.zipWith₃ (fun L₁ _ L₃ ↦ ¬ Lattice.IsSimilar R L₁ L₃) l l.tail l.tail.tail).Forall id
structure _root_.List.IsStandard (l : List (BruhatTits.Lattice R)) : Prop extends List.IsSimpleChain l where
  exists_basis : ∃ (b : Basis (Fin 2) K (Fin 2 → K)) (ϖ : R) (hϖ : Irreducible ϖ),
    l.zipIdx.Forall (fun (L, n) ↦ L = (b.ntwist₂ hϖ (l.length - n - 1) 0).toLattice)
instance : SMul (GL (Fin 2) K) (List (BruhatTits.Lattice R)) where
  smul g l := l.map (fun L ↦ g • L)
set_option synthInstance.maxHeartbeats 30000
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
end Chain
section TrafoStandard
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
end TrafoStandard
end BruhatTits


