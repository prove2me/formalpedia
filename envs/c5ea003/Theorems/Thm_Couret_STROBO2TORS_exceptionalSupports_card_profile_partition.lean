-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_exceptionalSupports_card_profile_partition
-- name    : Couret.STROBO2TORS.exceptionalSupports_card_profile_partition
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:26:04.553292+00:00
-- url     : https://prove2.me/theorems/4acb7bfd-a9b8-46c6-bc23-90dafe6f91d9
-- title:
--   Exceptional supports split into three profiles
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. Let $E$ be the exceptional supports and $E_j=\{S\in E:|S\cap H|=j\}$. Then
--
--   $$|E|=|E_0|+|E_1|+|E_2|.$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsExceptionalZero.lean, lines 75–100; source file SHA-256 65617a4490b73497cb28359bad8f2b27cd3159569e95b4ec095e4f4604f5eca0; theorem Couret.STROBO2TORS.exceptionalSupports_card_profile_partition

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupports_eq_three_profile_union
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports_card
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupportsProfile
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]

theorem exceptionalSupports_card_profile_partition :
    (exceptionalSupports : Finset (Finset G)).card =
      (exceptionalSupportsProfile (G := G) 0).card +
      (exceptionalSupportsProfile (G := G) 1).card +
      (exceptionalSupportsProfile (G := G) 2).card := by sorry








end Finite
end Couret.STROBO2TORS
