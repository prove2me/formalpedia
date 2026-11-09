-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroHitExceptionalFibres_weighted_card
-- name    : Couret.STROBO2TORS.zeroHitExceptionalFibres_weighted_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:13:32.555217+00:00
-- url     : https://prove2.me/theorems/4bcbb460-c824-4c34-9e39-8167dfe57a82
-- title:
--   Weighted count of zero-hit exceptional fibres
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. Let $\mathcal E_{\rm hit}$ be the exceptional fibres containing a support that contains zero. Then
--
--   $$2|\mathcal E_{\rm hit}|=3(h-1)(t-1).$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsZeroFree.lean, lines 263–281; source file SHA-256 5b8447d710c8e734bf9ff71c397ece8eebe34e569041c803c65dea8a9c580a24; theorem Couret.STROBO2TORS.zeroHitExceptionalFibres_weighted_card

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_member_card
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_zeroFree_card
import Theorems.Thm_Couret_STROBO2TORS_exceptionalParams_zero_card
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupports_eq_params_image
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_injective_on_exceptionalParams
import Theorems.Thm_Couret_STROBO2TORS_zeroContainingExceptionalSupports_preimage
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



section Finite

variable [Fintype G]

theorem zeroHitExceptionalFibres_weighted_card :
    2 * (zeroHitExceptionalFibres : Finset (Finset (Finset G))).card =
      3 * ((twoTorsion : Finset G).card - 1) * ((threeTorsion : Finset G).card - 1) := by sorry






































end Finite
end Couret.STROBO2TORS
