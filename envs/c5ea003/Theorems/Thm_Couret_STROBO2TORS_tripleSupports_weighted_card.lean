-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_tripleSupports_weighted_card
-- name    : Couret.STROBO2TORS.tripleSupports_weighted_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:39:51.427726+00:00
-- url     : https://prove2.me/theorems/ed48b3d9-c9cb-4c08-9b13-17cd1a381db7
-- title:
--   Weighted counting of ordinary and exceptional full fibres
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. Let $O,E$ be the numbers of ordinary and exceptional full triple square fibres. Then
--
--   $$\binom N3=h(O+2E).$$
--
--   Every support belongs to exactly one fibre, and its fibre has the corresponding uniform size.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsEnumeration.lean, lines 528–562; source file SHA-256 c5994a3923540d425df056cc4b93ff327cc2020eebfa6a424ceca158f26761bc; theorem Couret.STROBO2TORS.tripleSupports_weighted_card

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_allSquareFibres_eq_union
import Theorems.Thm_Couret_STROBO2TORS_allSquareFibres_preimage
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_member_card
import Theorems.Thm_Couret_STROBO2TORS_ordinary_exceptionalFibres_disjoint
import Theorems.Thm_Couret_STROBO2TORS_tripleSupports_card
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]

theorem tripleSupports_weighted_card :
    (Fintype.card G).choose 3 = (twoTorsion : Finset G).card *
      ((ordinaryFibres : Finset (Finset (Finset G))).card +
        2 * (exceptionalFibres : Finset (Finset (Finset G))).card) := by sorry






end Finite
end Couret.STROBO2TORS
