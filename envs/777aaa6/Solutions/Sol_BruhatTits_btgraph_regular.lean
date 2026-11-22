-- Prove2me | solution 1 for BruhatTits.btgraph_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:28:38.02818+00:00
-- url     : https://prove2.me/submissions/db2976fa-88d3-4d50-9406-2ed5b3b684dc

import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Definitions.Def_BruhatTits_Graph_Tree
import Definitions.Def_BruhatTits_Graph_Regular
import Theorems.Thm_BruhatTits_btgraph_degree

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
theorem _root_.solution :
    (BTgraph (R := R)).IsRegularOfDegree (Nat.card (ResidueField R) + 1) :=
  btgraph_degree
end BruhatTits
