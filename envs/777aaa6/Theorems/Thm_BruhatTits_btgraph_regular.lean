-- Prove2me | Theorems.Thm_BruhatTits_btgraph_regular
-- name    : BruhatTits.btgraph_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:26:23.334929+00:00
-- url     : https://prove2.me/theorems/89d0141e-bd7f-4587-89e7-354435f4d75f
-- title:
--   Bruhat Tits: btgraph regular
-- statement:
--   If `R ⧸ 𝓂 R` is finite, the Bruhat-Tits Tree is `q + 1`-regular, where `q` is the
--   cardinality of `R ⧸ 𝓂 R`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Regular.lean#L287-L289
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Regular.lean#L287-L289

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

theorem BruhatTits.btgraph_regular :
    (BTgraph (R := R)).IsRegularOfDegree (Nat.card (ResidueField R) + 1) := by sorry
