-- Prove2me | solution 1 for BruhatTits.btgraph_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:26:14.031301+00:00
-- url     : https://prove2.me/submissions/62ff31ea-0d52-48ec-8327-8a1ce86bc034

import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Definitions.Def_BruhatTits_Graph_Tree
import Definitions.Def_BruhatTits_Graph_Regular

set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]
open BruhatTits
open IsLocalRing
open Pointwise
open scoped LinearAlgebra.Projectivization
variable [Finite (ResidueField R)]
namespace BruhatTits
theorem _root_.solution (x : Vertices R) :
    (BTgraph (R := R)).degree x = Nat.card (ResidueField R) + 1 := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card]
  refine Quotient.inductionOn x (fun L ↦ ?_)
  rw [Nat.card_congr (neighborSetEquivProjectivization L)]
  apply Projectivization.card_of_finrank_two
  exact Lattice.quotient_finrank L
end BruhatTits
