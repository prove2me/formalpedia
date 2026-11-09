-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_full_card
-- name    : Couret.STROBO2TORS.zeroFreeExceptionalFibres_full_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:18:17.870111+00:00
-- url     : https://prove2.me/theorems/8afed410-41f1-41fa-9003-454858b5dd69
-- title:
--   Count of full-size zero-free exceptional fibres
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. Let $q=|2G|$ and let $s_3$ be the number of nonzero three-torsion sign pairs $\{v,-v\}$. Then $$|\{F\in\mathcal E^\circ:|F|=2h\}|=(q-3)(h-1)s_3.$$
--
--   The family $\mathcal E^\circ$ consists of the nonempty zero-free exceptional fibre parts; natural subtraction is used.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsZeroFree.lean, lines 434–440; source file SHA-256 5b8447d710c8e734bf9ff71c397ece8eebe34e569041c803c65dea8a9c580a24; theorem Couret.STROBO2TORS.zeroFreeExceptionalFibres_full_card

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_card_product
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_filter_full_eq
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_preimage
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_withoutZero_card_ge_two
import Theorems.Thm_Couret_STROBO2TORS_threeTorsion_nonzero_card_eq_two_pairs
import Theorems.Thm_Couret_STROBO2TORS_zeroHitExceptionalFibres_weighted_card
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



section Finite

variable [Fintype G]

theorem zeroFreeExceptionalFibres_full_card :
    ((zeroFreeExceptionalFibres : Finset (Finset (Finset G))).filter
      (fun F => F.card = 2 * (twoTorsion : Finset G).card)).card =
      ((doublingImages : Finset G).card - 3) * ((twoTorsion : Finset G).card - 1) *
        (threeSignPairs : Finset (Finset G)).card := by sorry






end Finite
end Couret.STROBO2TORS
