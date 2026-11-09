-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_histogram_numeric
-- name    : Couret.STROBO2TORS.zeroFreeFullFibres_histogram_numeric
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:59:15.902204+00:00
-- url     : https://prove2.me/theorems/0aa42558-f095-4ed2-a9de-4ce18be1144e
-- title:
--   A closed numerical histogram of all observed zero-free fibres
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. Let $\mathcal F^*$ be all nonempty zero-free triple square fibres, and put $p=(t-1)/2$. Define
--
--   $$A_0=\bigl(\binom h0\binom{N-h}3-(N-2h)(h-1)(t-1)\bigr)/h,$$
--   $$A_1=\bigl(\binom h1\binom{N-h}2-h(h-1)(t-1)\bigr)/h,$$
--   $$A_2=\bigl(\binom h2\binom{N-h}1-h(h-1)(t-1)\bigr)/h,\qquad A_3=\binom h3/h.$$
--
--   For every $k>0$,
--
--   $$|\{R\in\mathcal F^*:|R|=k\}|=\sum_{j=0}^3\mathbf1_{h-j=k}A_j+\mathbf1_{k=2h-2}3(h-1)p+\mathbf1_{k=2h}(D-3)(h-1)p.$$
--
--   Each subtraction, including $N-2h$ inside $A_0$, is truncated at zero before further arithmetic.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsClosedHistogram.lean, lines 175–219; source file SHA-256 584fb4d377d4eb190f2bc36949a4c3596cb755c509c4441a3e6c1c3c26d6477c; theorem Couret.STROBO2TORS.zeroFreeFullFibres_histogram_numeric

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibresProfile_card_one_numeric
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibresProfile_card_three
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibresProfile_card_two_numeric
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibresProfile_card_zero_numeric
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_histogram_formula
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_histogram_partition
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeOrdinaryFibres_histogram_by_profiles
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]

theorem zeroFreeFullFibres_histogram_numeric (k : ℕ) (hk : 0 < k) :
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
          (threeSignPairs : Finset (Finset G)).card else 0) +
      (if k = 2 * (twoTorsion : Finset G).card then
        ((doublingImages : Finset G).card - 3) *
          ((twoTorsion : Finset G).card - 1) *
          (threeSignPairs : Finset (Finset G)).card else 0) := by sorry


end Finite
end Couret.STROBO2TORS
