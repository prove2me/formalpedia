-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_threeSignPairs_card_division
-- name    : Couret.STROBO2TORS.threeSignPairs_card_division
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:01:21.613769+00:00
-- url     : https://prove2.me/theorems/d41305b5-4bc1-45e9-9234-d2f3a9e521a2
-- title:
--   Number of nonzero three-torsion sign pairs
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. Let $\mathcal P=\{\{v,-v\}:v\in G[3]\setminus\{0\}\}$. Then
--
--   $$|\mathcal P|=(t-1)/2.$$
--
--   Each pair has two elements, since no nonzero three-torsion element is its own negative.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsEnumeration.lean, lines 427–430; source file SHA-256 c5994a3923540d425df056cc4b93ff327cc2020eebfa6a424ceca158f26761bc; theorem Couret.STROBO2TORS.threeSignPairs_card_division

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_threeTorsion_nonzero_card_eq_two_pairs
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]

theorem threeSignPairs_card_division :
    (threeSignPairs : Finset (Finset G)).card = ((threeTorsion : Finset G).card - 1) / 2 := by sorry






























end Finite
end Couret.STROBO2TORS
