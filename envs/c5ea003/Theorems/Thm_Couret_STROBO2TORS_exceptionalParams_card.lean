-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_exceptionalParams_card
-- name    : Couret.STROBO2TORS.exceptionalParams_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:27.659242+00:00
-- url     : https://prove2.me/theorems/fdd86a92-71be-4ba7-bfd5-a5cef30b5772
-- title:
--   Number of exceptional support parameters
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. The parameter set $\mathcal A=G\times(H\setminus\{0\})\times(K\setminus\{0\})$ satisfies
--
--   $$|\mathcal A|=n(h-1)(t-1).$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsEnumeration.lean, lines 162–179; source file SHA-256 c5994a3923540d425df056cc4b93ff327cc2020eebfa6a424ceca158f26761bc; theorem Couret.STROBO2TORS.exceptionalParams_card

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_threeTorsion
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]

theorem exceptionalParams_card :
    (exceptionalParams : Finset ((G × G) × G)).card =
      Fintype.card G * ((twoTorsion : Finset G).card - 1) * ((threeTorsion : Finset G).card - 1) := by sorry










































































end Finite
end Couret.STROBO2TORS
