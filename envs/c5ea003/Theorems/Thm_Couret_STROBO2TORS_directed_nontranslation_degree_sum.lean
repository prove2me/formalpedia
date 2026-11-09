-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_directed_nontranslation_degree_sum
-- name    : Couret.STROBO2TORS.directed_nontranslation_degree_sum
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:43.386595+00:00
-- url     : https://prove2.me/theorems/466acce7-7726-4092-8a48-8f348cb45c46
-- title:
--   Directed nontranslation degree sum
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. Let $E$ be the set of exceptional triple supports, and $V$ all three-element supports. Then
--
--   $$\sum_{S\in V}|F(S)\setminus O(S)|=|E|h.$$
--
--   Each nontranslation neighbour contributes in the direction of its source support.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsNontranslationDegree.lean, lines 81–120; source file SHA-256 bb81c661856c1b823aeeb307e2603c5cb0aee20a082885d1c0ea1a2cc7b78ead; theorem Couret.STROBO2TORS.directed_nontranslation_degree_sum

import Aesop
import Definitions.Def_Couret_Strobo2TorsNontranslationDegree_16ff2822736a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports_card
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
import Theorems.Thm_Couret_STROBO2TORS_nontranslatedNeighbours_card_exceptional
import Theorems.Thm_Couret_STROBO2TORS_nontranslatedNeighbours_card_ordinary
import Definitions.Def_Couret_Strobo2TorsNontranslationBridge_e18319b1ae30
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem directed_nontranslation_degree_sum :
    (∑ S ∈ (tripleSupports : Finset (Finset G)),
        (nontranslatedNeighbours S).card) =
      (exceptionalSupports : Finset (Finset G)).card *
        (twoTorsion : Finset G).card := by sorry




end Couret.STROBO2TORS
