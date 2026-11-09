-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_card_of_four
-- name    : Couret.STROBO2TORS.zeroFreeFullFibres_card_of_four
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:43:46.373199+00:00
-- url     : https://prove2.me/theorems/825b1fa2-92ff-40a3-8bd5-32de351cf506
-- title:
--   All fibres survive zero deletion when two-torsion has size at least four
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. If $h\ge4$, and $\mathcal Z$ is the family of observed nonempty zero-free full fibres, then
--
--   $$|\mathcal Z|=|\mathcal U|+|\mathcal E|,$$
--
--   where $\mathcal U$ and $\mathcal E$ are the ordinary and exceptional full fibres.
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsSurvivalCounts.lean, lines 68–85; source file SHA-256 eb83aad035d165b4936c91ba5553308053fd7af14d21de79283c272887a1f571; theorem Couret.STROBO2TORS.zeroFreeFullFibres_card_of_four

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_allSquareFibres_eq_union
import Theorems.Thm_Couret_STROBO2TORS_nonemptyFullFibres_eq_union
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibres_nonempty_of_four
import Theorems.Thm_Couret_STROBO2TORS_ordinary_exceptionalFibres_disjoint
import Theorems.Thm_Couret_STROBO2TORS_withoutZero_injective_on_nonemptyFullFibres
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

theorem zeroFreeFullFibres_card_of_four
    (hh : 4 ≤ (twoTorsion : Finset G).card) :
    (zeroFreeFullFibres : Finset (Finset (Finset G))).card =
      (ordinaryFibres : Finset (Finset (Finset G))).card +
        (exceptionalFibres : Finset (Finset (Finset G))).card := by sorry






end Finite
end Couret.STROBO2TORS
