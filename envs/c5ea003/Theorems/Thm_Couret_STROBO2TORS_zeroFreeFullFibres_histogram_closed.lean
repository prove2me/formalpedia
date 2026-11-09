-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_histogram_closed
-- name    : Couret.STROBO2TORS.zeroFreeFullFibres_histogram_closed
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:58:23.472721+00:00
-- url     : https://prove2.me/theorems/f1bb2f3e-1e31-460b-8632-a45cc602dcf1
-- title:
--   Closed histogram of zero-free fibre sizes
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. Let $\mathcal Z$ be the family of observed nonempty zero-free full fibres and let $k>0$. Set $s=(t-1)/2$ and define $e_0=(n-2h)(h-1)(t-1)$, $e_1=e_2=h(h-1)(t-1)$, $e_3=0$, and $a_j=(\binom hj\binom{n-h}{3-j}-e_j)/h$ for $0\le j\le3$. Then
--
--   $$\#\{R\in\mathcal Z:|R|=k\}=\sum_{j=0}^3[k=h-j]a_j+[k=2h-2]3(h-1)s+[k=2h](n/h-3)(h-1)s.$$
--
--   Brackets are indicators. All subtractions and divisions in these definitions use natural-number arithmetic, including truncation at zero.
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsHistogram.lean, lines 182–226; source file SHA-256 c12ab039c6b1ab4ff961876e1b2df183771e0e7ecfaff3c058cae2eec9da35b0; theorem Couret.STROBO2TORS.zeroFreeFullFibres_histogram_closed

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_doublingImages_card_division
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibresProfile_card_one_numeric
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibresProfile_card_three
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibresProfile_card_two_numeric
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibresProfile_card_zero_numeric
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibres_histogram_by_profile
import Theorems.Thm_Couret_STROBO2TORS_threeSignPairs_card_division
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_histogram_semi_numeric
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

theorem zeroFreeFullFibres_histogram_closed (k : ℕ) (hk : 0 < k) :
    ((zeroFreeFullFibres : Finset (Finset (Finset G))).filter
      (fun R => R.card = k)).card =
      (if (twoTorsion : Finset G).card = k then
        (((twoTorsion : Finset G).card.choose 0) *
          ((Fintype.card G - (twoTorsion : Finset G).card).choose 3) -
          ((Fintype.card G - 2 * (twoTorsion : Finset G).card) *
            ((twoTorsion : Finset G).card - 1) *
            ((threeTorsion : Finset G).card - 1))) /
            (twoTorsion : Finset G).card else 0) +
      (if (twoTorsion : Finset G).card - 1 = k then
        (((twoTorsion : Finset G).card.choose 1) *
          ((Fintype.card G - (twoTorsion : Finset G).card).choose 2) -
          ((twoTorsion : Finset G).card *
            ((twoTorsion : Finset G).card - 1) *
            ((threeTorsion : Finset G).card - 1))) /
            (twoTorsion : Finset G).card else 0) +
      (if (twoTorsion : Finset G).card - 2 = k then
        (((twoTorsion : Finset G).card.choose 2) *
          ((Fintype.card G - (twoTorsion : Finset G).card).choose 1) -
          ((twoTorsion : Finset G).card *
            ((twoTorsion : Finset G).card - 1) *
            ((threeTorsion : Finset G).card - 1))) /
            (twoTorsion : Finset G).card else 0) +
      (if (twoTorsion : Finset G).card - 3 = k then
        ((twoTorsion : Finset G).card.choose 3) /
          (twoTorsion : Finset G).card else 0) +
      (if k = 2 * (twoTorsion : Finset G).card - 2 then
        3 * ((twoTorsion : Finset G).card - 1) *
          (((threeTorsion : Finset G).card - 1) / 2) else 0) +
      (if k = 2 * (twoTorsion : Finset G).card then
        ((Fintype.card G / (twoTorsion : Finset G).card) - 3) *
          ((twoTorsion : Finset G).card - 1) *
          (((threeTorsion : Finset G).card - 1) / 2) else 0) := by sorry


end Finite
end Couret.STROBO2TORS
