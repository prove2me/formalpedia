-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_nontranslationDeltaGraph_degree_four
-- name    : Couret.STROBO2TORS.nontranslationDeltaGraph_degree_four
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:17:45.709386+00:00
-- url     : https://prove2.me/theorems/2a94c8b7-4cf4-4d2d-b804-8b5c7cfc1118
-- title:
--   Nontranslation delta-four degree is an exceptional indicator
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. In the graph joining nontranslated square-equivalent triples with symmetric-difference size four, every finite support $S$ has degree
--
--   $$\deg_4(S)=\begin{cases}1,&S\text{ exceptional},\\0,&\text{otherwise}.\end{cases}$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaExceptionalCount.lean, lines 224–240; source file SHA-256 f29a05e63c72c6391cb5af4eda72214b169f1bd248608234ab836d615b0d4ef0; theorem Couret.STROBO2TORS.nontranslationDeltaGraph_degree_four

import Aesop
import Definitions.Def_Couret_Strobo2TorsDeltaExceptionalCount_9f9783d90924
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalPartner_normalized_inter
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports
import Theorems.Thm_Couret_STROBO2TORS_nontranslatedNeighbours_card_ordinary
import Theorems.Thm_Couret_STROBO2TORS_paired_orbits_disjoint
import Theorems.Thm_Couret_STROBO2TORS_paired_squareFibre_eq
import Theorems.Thm_Couret_STROBO2TORS_paired_support_card_three
import Theorems.Thm_Couret_STROBO2TORS_reflected_support_card_three
import Theorems.Thm_Couret_STROBO2TORS_triple_symmDiff_card_balance
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Definitions.Def_Couret_Strobo2TorsNontranslationUnordered_7692bff20374

set_option autoImplicit false

/-!
Unordered nontranslation collisions, split by symmetric-difference size.
The ambient group is finite abelian, supports have cardinality three, and
zero is permitted. An exceptional source has one delta-four neighbour and
`|G[2]| - 1` delta-six neighbours. Graph degree sums count unordered pairs
twice, so the final statements require no division in natural numbers.
-/

open scoped BigOperators symmDiff

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem nontranslationDeltaGraph_degree_four (S : Finset G) :
    (nontranslationDeltaGraph (G := G) 4).degree S =
      if S ∈ (exceptionalSupports : Finset (Finset G)) then 1 else 0 := by sorry















end Couret.STROBO2TORS
