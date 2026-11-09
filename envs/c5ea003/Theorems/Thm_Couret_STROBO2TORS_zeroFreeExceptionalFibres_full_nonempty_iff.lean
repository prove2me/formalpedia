-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_full_nonempty_iff
-- name    : Couret.STROBO2TORS.zeroFreeExceptionalFibres_full_nonempty_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:21:43.380755+00:00
-- url     : https://prove2.me/theorems/dfc0140b-322c-4894-a6e5-30d442ad5dbd
-- title:
--   When full-size zero-free exceptional fibres exist
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. There is an exceptional fibre whose zero-free part retains size $2h$ if and only if
--
--   $$q>3,\qquad h>1,\qquad t>1.$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsZeroFree.lean, lines 442–460; source file SHA-256 5b8447d710c8e734bf9ff71c397ece8eebe34e569041c803c65dea8a9c580a24; theorem Couret.STROBO2TORS.zeroFreeExceptionalFibres_full_nonempty_iff

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_threeTorsion_nonzero_card_eq_two_pairs
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_full_card
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



section Finite

variable [Fintype G]

theorem zeroFreeExceptionalFibres_full_nonempty_iff :
    ((zeroFreeExceptionalFibres : Finset (Finset (Finset G))).filter
      (fun F => F.card = 2 * (twoTorsion : Finset G).card)).Nonempty ↔
      3 < (doublingImages : Finset G).card ∧ 1 < (twoTorsion : Finset G).card ∧
        1 < (threeTorsion : Finset G).card := by sorry




end Finite
end Couret.STROBO2TORS
