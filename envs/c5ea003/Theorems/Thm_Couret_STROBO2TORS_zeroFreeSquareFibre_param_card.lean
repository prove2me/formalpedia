-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeSquareFibre_param_card
-- name    : Couret.STROBO2TORS.zeroFreeSquareFibre_param_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:56:18.100221+00:00
-- url     : https://prove2.me/theorems/a1388710-4bbb-421e-a299-2f5c9283ba82
-- title:
--   Zero-free size of a canonically exceptional fibre
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. Let $S=\{a,a+v,a+v+d\}$, where $d\ne0$, $2d=0$, $v\ne0$ and $3v=0$. Then
--
--   $$|F(S)^*|=\begin{cases}2h-2&2a=0\lor2(a+v)=0\lor2(a-v)=0,\\2h&\text{otherwise}.\end{cases}$$
--
--   This distinguishes the reduced and unreduced exceptional sizes.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsZeroFree.lean, lines 70–109; source file SHA-256 5b8447d710c8e734bf9ff71c397ece8eebe34e569041c803c65dea8a9c580a24; theorem Couret.STROBO2TORS.zeroFreeSquareFibre_param_card

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptional_param_genuine
import Theorems.Thm_Couret_STROBO2TORS_paired_zeroFreeSquareFibre_card
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_inter_twoTorsion_card
import Theorems.Thm_Couret_STROBO2TORS_three_torsion_double_eq_neg
import Theorems.Thm_Couret_STROBO2TORS_three_torsion_neg
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_ge_two
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



section Finite

variable [Fintype G]

theorem zeroFreeSquareFibre_param_card (a d v : G)
    (hd : d + d = 0) (hd0 : d ≠ 0) (hv : (v + v) + v = 0) (hv0 : v ≠ 0) :
    (zeroFreeSquareFibre (paramSupport ((a, d), v))).card =
      if a + a = 0 ∨ (a + v) + (a + v) = 0 ∨ (a - v) + (a - v) = 0
      then 2 * (twoTorsion : Finset G).card - 2 else 2 * (twoTorsion : Finset G).card := by sorry




































































end Finite
end Couret.STROBO2TORS
