-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_ordinaryFibresProfile_filter_size_card
-- name    : Couret.STROBO2TORS.ordinaryFibresProfile_filter_size_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:26:06.973867+00:00
-- url     : https://prove2.me/theorems/9f5035b7-1046-4da4-bb0f-7b49a608bfa5
-- title:
--   Zero-free size is determined by an ordinary fibre profile
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. For $j,k\in\mathbb N$, let $\mathcal O_j$ be ordinary full fibres having a member $S$ with $|S\cap H|=j$. Then
--
--   $$|\{F\in\mathcal O_j:|F^*|=k\}|=\begin{cases}|\mathcal O_j|&h-j=k,\\0&\text{otherwise}.\end{cases}$$
--
--   Natural subtraction is used even for out-of-range profiles.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsHistogram.lean, lines 83–116; source file SHA-256 c12ab039c6b1ab4ff961876e1b2df183771e0e7ecfaff3c058cae2eec9da35b0; theorem Couret.STROBO2TORS.ordinaryFibresProfile_filter_size_card

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibresProfile_zeroFree_card
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

theorem ordinaryFibresProfile_filter_size_card (j k : ℕ) :
    ((ordinaryFibresProfile (G := G) j).filter
      (fun F => (withoutZero F).card = k)).card =
      if (twoTorsion : Finset G).card - j = k then
        (ordinaryFibresProfile (G := G) j).card else 0 := by sorry






end Finite
end Couret.STROBO2TORS
