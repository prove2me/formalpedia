-- Prove2me | Theorems.Thm_BruhatTits_btgraph_degree
-- name    : BruhatTits.btgraph_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:26:10.415662+00:00
-- url     : https://prove2.me/theorems/28008499-a551-4590-b8f0-b6ccecefb2e2
-- title:
--   Bruhat Tits: btgraph degree
-- statement:
--   The degree of the Bruhat-Tits tree is `q + 1` where `q` is the cardinality of `R ⧸ 𝓂 R`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Regular.lean#L277-L283
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Regular.lean#L277-L283

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

theorem BruhatTits.btgraph_degree (x : Vertices R) :
    (BTgraph (R := R)).degree x = Nat.card (ResidueField R) + 1 := by sorry
