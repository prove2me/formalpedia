-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_pairParameters_card
-- name    : Couret.STROBO2TORS.pairParameters_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:39:04.191961+00:00
-- url     : https://prove2.me/theorems/a1371298-0659-461d-a181-9eb931c73915
-- title:
--   The number of zero-free nontranslation-pair parameters
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. Let $P(a,d,v)=\{a,a+v,a+v+d\}$. Count quadruples $(d,v,a,u)$ with $d\in H\setminus\{0\}$, $v\in G[3]\setminus\{0\}$, $a\in G$, $u\in H$, and neither $P(a,d,v)$ nor $P(a,d,-v)+u$ containing zero. Their number is
--
--   $$(h-1)(t-1)((Nh-6h)+1).$$
--
--   The subtraction occurs before the final addition.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsPairCount.lean, lines 282–300; source file SHA-256 f6c997c461f640aab1856a21d5adfad3e6bfdbf876e67e5783b3ba87b26827cd; theorem Couret.STROBO2TORS.pairParameters_card

import Aesop
import Definitions.Def_Couret_Strobo2TorsPairCount_5c76f0dc12bb
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_threeTorsion
import Theorems.Thm_Couret_STROBO2TORS_pairLifts_card_balance
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_ge_two
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators
namespace Couret.STROBO2TORS
variable {G : Type*} [AddCommGroup G] [DecidableEq G]







section Finite
variable [Fintype G]

theorem pairParameters_card :
    (pairParameters : Finset (PairParameter G)).card =
      ((twoTorsion : Finset G).card-1) * ((threeTorsion : Finset G).card-1) *
        (Fintype.card G * (twoTorsion : Finset G).card - 6 * (twoTorsion : Finset G).card + 1) := by sorry




attribute [local instance] Classical.propDecidable





























end Finite
end Couret.STROBO2TORS
