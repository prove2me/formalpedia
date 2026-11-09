-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_ordinaryGraph_neighborFinset
-- name    : Couret.STROBO2TORS.ordinaryGraph_neighborFinset
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:01:33.816141+00:00
-- url     : https://prove2.me/theorems/e14f8729-71c9-4858-8c13-2f34a7783298
-- title:
--   Ordinary graph neighbours are the orbit minus the vertex
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. For every finite support $S$, the neighbour family in the ordinary-partner graph is
--
--   $$N_{\rm ord}(S)=\begin{cases}\mathcal O(S)\setminus\{S\},&|S|=3,\\\varnothing,&|S|\ne3.\end{cases}$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaOrdinaryCount.lean, lines 37–55; source file SHA-256 5f469c556c1bf01d2004ee02931f1320ffd1877ea4f76323ea4b587ca2c42c59; theorem Couret.STROBO2TORS.ordinaryGraph_neighborFinset

import Aesop
import Definitions.Def_Couret_Strobo2TorsDeltaOrdinaryCount_91279c99d3e0
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option autoImplicit false

open scoped BigOperators symmDiff

/-!
Ordinary collision edges on all triple supports, with zero permitted.
The action of the two-torsion subgroup is free on a three-element support.
Consequently every triple has exactly h - 1 distinct ordinary neighbours.
The certified intersection subdivision partitions these edges into delta
two and delta six; this module does not identify ordinary fibres with all
ordinary partner edges, since exceptional fibres contain such edges too.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem ordinaryGraph_neighborFinset (S : Finset G) :
    (ordinaryGraph (G := G)).neighborFinset S =
      if S.card = 3 then (torsionOrbit S).erase S else ∅ := by sorry























end Couret.STROBO2TORS
