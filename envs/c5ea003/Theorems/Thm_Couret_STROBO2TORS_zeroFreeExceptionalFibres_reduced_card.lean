-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_reduced_card
-- name    : Couret.STROBO2TORS.zeroFreeExceptionalFibres_reduced_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:16:41.35813+00:00
-- url     : https://prove2.me/theorems/1ff4beb2-5bd4-4b2b-8f79-1d284d5215ea
-- title:
--   Number of reduced zero-free exceptional fibres
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. Let $\mathcal E^\circ=\{F^\circ:F\text{ exceptional}\}$ and $s=|\{\{v,-v\}:v\in K\setminus\{0\}\}|$. Then
--
--   $$\#\{R\in\mathcal E^\circ:|R|=2h-2\}=3(h-1)s.$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsZeroFree.lean, lines 427–432; source file SHA-256 5b8447d710c8e734bf9ff71c397ece8eebe34e569041c803c65dea8a9c580a24; theorem Couret.STROBO2TORS.zeroFreeExceptionalFibres_reduced_card

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_filter_reduced_eq
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

theorem zeroFreeExceptionalFibres_reduced_card :
    ((zeroFreeExceptionalFibres : Finset (Finset (Finset G))).filter
      (fun F => F.card = 2 * (twoTorsion : Finset G).card - 2)).card =
      3 * ((twoTorsion : Finset G).card - 1) * (threeSignPairs : Finset (Finset G)).card := by sorry








end Finite
end Couret.STROBO2TORS
