-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_ordinaryGraph_twice_edges
-- name    : Couret.STROBO2TORS.ordinaryGraph_twice_edges
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:16:43.726815+00:00
-- url     : https://prove2.me/theorems/7de34859-3319-40f3-a37c-2c4a5c15d31b
-- title:
--   The total number of ordinary collision edges
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. If $e_O$ is the number of unordered edges joining distinct ordinary triple partners, then
--
--   $$2e_O=\binom N3(h-1).$$
--
--   Each three-element support has exactly $h-1$ other ordinary partners.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaOrdinaryCount.lean, lines 72–101; source file SHA-256 5f469c556c1bf01d2004ee02931f1320ffd1877ea4f76323ea4b587ca2c42c59; theorem Couret.STROBO2TORS.ordinaryGraph_twice_edges

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
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
import Theorems.Thm_Couret_STROBO2TORS_ordinaryGraph_neighborFinset
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_card
import Theorems.Thm_Couret_STROBO2TORS_tripleSupports_card
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

theorem ordinaryGraph_twice_edges :
    2 * (ordinaryGraph (G := G)).edgeFinset.card =
      (Fintype.card G).choose 3 * ((twoTorsion : Finset G).card - 1) := by sorry



















end Couret.STROBO2TORS
