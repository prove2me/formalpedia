-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_ordinaryFibres_eq_profile_union_alternative
-- name    : Couret.STROBO2TORS.ordinaryFibres_eq_profile_union_alternative
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:26:03.257913+00:00
-- url     : https://prove2.me/theorems/0c47db4b-1aab-428c-8be9-970c86b1d3d4
-- title:
--   Ordinary fibres are exhausted by profiles zero through three
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. With $\mathcal U_j$ the ordinary fibres containing a profile-$j$ support,
--
--   $$\mathcal U=\mathcal U_0\cup\mathcal U_1\cup\mathcal U_2\cup\mathcal U_3.$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsHistogram.lean, lines 36–69; source file SHA-256 c12ab039c6b1ab4ff961876e1b2df183771e0e7ecfaff3c058cae2eec9da35b0; theorem Couret.STROBO2TORS.ordinaryFibres_eq_profile_union_alternative

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

theorem ordinaryFibres_eq_profile_union_alternative :
    (ordinaryFibres : Finset (Finset (Finset G))) =
      ordinaryFibresProfile 0 ∪
        (ordinaryFibresProfile 1 ∪
          (ordinaryFibresProfile 2 ∪ ordinaryFibresProfile 3)) := by sorry










end Finite
end Couret.STROBO2TORS
