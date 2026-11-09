-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_nontranslationDeltaGraph_degree_six
-- name    : Couret.STROBO2TORS.nontranslationDeltaGraph_degree_six
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:51.558258+00:00
-- url     : https://prove2.me/theorems/98c02cf4-8561-4c4f-bddc-4a757114e238
-- title:
--   Degree in the disjoint nontranslation collision graph
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. Join supports of size three when they have equal ordered squares, are not translates, and have symmetric difference of size six. For any finite support $S$,
--
--   $$\deg(S)=\begin{cases}h-1&S\text{ exceptional},\\0&\text{otherwise}.\end{cases}$$
--
--   Nontriples have degree zero.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaExceptionalCount.lean, lines 242–259; source file SHA-256 f29a05e63c72c6391cb5af4eda72214b169f1bd248608234ab836d615b0d4ef0; theorem Couret.STROBO2TORS.nontranslationDeltaGraph_degree_six

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
import Theorems.Thm_Couret_STROBO2TORS_nontranslatedNeighbours_card_exceptional
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

theorem nontranslationDeltaGraph_degree_six (S : Finset G) :
    (nontranslationDeltaGraph (G := G) 6).degree S =
      if S ∈ (exceptionalSupports : Finset (Finset G))
      then (twoTorsion : Finset G).card - 1 else 0 := by sorry













end Couret.STROBO2TORS
