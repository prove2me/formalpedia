-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_allSquareFibres_eq_union
-- name    : Couret.STROBO2TORS.allSquareFibres_eq_union
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:56:42.509576+00:00
-- url     : https://prove2.me/theorems/87d13188-7886-4d96-bd20-eb93e4b73264
-- title:
--   All square fibres split into ordinary and exceptional families
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. Let $\mathcal F,\mathcal O,\mathcal E$ denote respectively all three-support square fibres and the ordinary and exceptional fibre families. Then $$\mathcal F=\mathcal O\cup\mathcal E.$$
--
--   This is equality of finite families.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsEnumeration.lean, lines 481–500; source file SHA-256 c5994a3923540d425df056cc4b93ff327cc2020eebfa6a424ceca158f26761bc; theorem Couret.STROBO2TORS.allSquareFibres_eq_union

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_eq_all_filter
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports_card
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_card_h_or_two_h
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]

theorem allSquareFibres_eq_union :
    (allSquareFibres : Finset (Finset (Finset G))) = ordinaryFibres ∪ exceptionalFibres := by sorry












end Finite
end Couret.STROBO2TORS
