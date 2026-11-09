-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_weighted_card
-- name    : Couret.STROBO2TORS.exceptionalFibres_weighted_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:12:23.553647+00:00
-- url     : https://prove2.me/theorems/e2a037d6-9646-4c59-b8a4-c2e6b8664494
-- title:
--   Weighted exceptional-fibre count
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. If $\mathcal E$ denotes the exceptional fibres, then
--
--   $$2h|\mathcal E|=n(h-1)(t-1).$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsEnumeration.lean, lines 279–298; source file SHA-256 c5994a3923540d425df056cc4b93ff327cc2020eebfa6a424ceca158f26761bc; theorem Couret.STROBO2TORS.exceptionalFibres_weighted_card

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_member_card
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_preimage
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupports_card
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]

theorem exceptionalFibres_weighted_card :
    (2 * (twoTorsion : Finset G).card) *
      (exceptionalFibres : Finset (Finset (Finset G))).card =
      Fintype.card G * ((twoTorsion : Finset G).card - 1) * ((threeTorsion : Finset G).card - 1) := by sorry
























































end Finite
end Couret.STROBO2TORS
