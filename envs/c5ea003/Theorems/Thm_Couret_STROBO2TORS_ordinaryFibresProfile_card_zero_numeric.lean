-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_ordinaryFibresProfile_card_zero_numeric
-- name    : Couret.STROBO2TORS.ordinaryFibresProfile_card_zero_numeric
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:44:29.334388+00:00
-- url     : https://prove2.me/theorems/14cef860-76d0-41ac-8f58-4d29022e572b
-- title:
--   Numeric count of ordinary profile-zero fibres
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. Let $\mathcal U_0$ be the ordinary fibres with zero torsion elements per support. Then
--
--   $$|\mathcal U_0|=\frac{\binom h0\binom{n-h}3-(n-2h)(h-1)(t-1)}{h}.$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsExceptionalZero.lean, lines 131–143; source file SHA-256 65617a4490b73497cb28359bad8f2b27cd3159569e95b4ec095e4f4604f5eca0; theorem Couret.STROBO2TORS.ordinaryFibresProfile_card_zero_numeric

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupportsProfile_one_card
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupportsProfile_two_card
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupports_card
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupports_card_profile_partition
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibresProfile_card_sub_div
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]

theorem ordinaryFibresProfile_card_zero_numeric :
    (ordinaryFibresProfile (G := G) 0).card =
      (((twoTorsion : Finset G).card.choose 0) *
          ((Fintype.card G - (twoTorsion : Finset G).card).choose 3) -
        ((Fintype.card G - 2 * (twoTorsion : Finset G).card) *
          ((twoTorsion : Finset G).card - 1) *
          ((threeTorsion : Finset G).card - 1))) /
        (twoTorsion : Finset G).card := by sorry


end Finite
end Couret.STROBO2TORS
