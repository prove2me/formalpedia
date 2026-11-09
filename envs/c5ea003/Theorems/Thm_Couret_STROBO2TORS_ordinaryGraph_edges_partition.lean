-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_ordinaryGraph_edges_partition
-- name    : Couret.STROBO2TORS.ordinaryGraph_edges_partition
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:16:46.362765+00:00
-- url     : https://prove2.me/theorems/1d1913ae-227a-4872-9757-db94eb3c3d1d
-- title:
--   Ordinary edges partition by distances two and six
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. For the ordinary collision graph $\Gamma^{\mathrm{ord}}$, $$|E(\Gamma^{\mathrm{ord}})|=|E(\Gamma^{\mathrm{ord}}_2)|+|E(\Gamma^{\mathrm{ord}}_6)|.$$ No other symmetric-difference size contributes ordinary edges.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaOrdinaryCount.lean, lines 181–202; source file SHA-256 5f469c556c1bf01d2004ee02931f1320ffd1877ea4f76323ea4b587ca2c42c59; theorem Couret.STROBO2TORS.ordinaryGraph_edges_partition

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
import Theorems.Thm_Couret_STROBO2TORS_ordinaryGraph_degree_partition
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

theorem ordinaryGraph_edges_partition :
    (ordinaryGraph (G := G)).edgeFinset.card =
      (ordinaryDeltaGraph (G := G) 2).edgeFinset.card +
        (ordinaryDeltaGraph (G := G) 6).edgeFinset.card := by sorry





end Couret.STROBO2TORS
