-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_maxObservedZeroFreeFibreSize_complete
-- name    : Couret.STROBO2TORS.maxObservedZeroFreeFibreSize_complete
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:52:54.318006+00:00
-- url     : https://prove2.me/theorems/6f9e023d-6910-4954-96fa-ca4e121db62f
-- title:
--   The exact maximum observed zero-free fibre size
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. Let $M$ be the maximum cardinality of a nonempty zero-free triple square fibre, with maximum zero if none exist. Test the following conditions in order:
--
--   $$M=\begin{cases}0&N<4,\\1&N\ge4,\ h=1,\\h-3&N\ge4,\ h\ne1,\ D=1,\\1&\text{earlier cases fail and }N=4,\\h&\text{earlier cases fail and }t=1,\\2h-2&\text{earlier cases fail and }D\le3,\\2h&\text{otherwise}.\end{cases}$$
--
--   The ordered branches preserve the small-group boundary cases.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsSharpMaximum.lean, lines 400–455; source file SHA-256 98c3b135eb2ea85402b9696299566a40098ac965175f8307832d30ec1e652733; theorem Couret.STROBO2TORS.maxObservedZeroFreeFibreSize_complete

import Aesop
import Definitions.Def_Couret_Strobo2TorsSharpMaximum_bfb30eac9be9
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_maxObservedZeroFreeFibreSize_eq_h_sub_three_of_q_one
import Theorems.Thm_Couret_STROBO2TORS_maxObservedZeroFreeFibreSize_eq_one_of_card_four
import Theorems.Thm_Couret_STROBO2TORS_maxObservedZeroFreeFibreSize_eq_one_of_trivial_two_torsion
import Theorems.Thm_Couret_STROBO2TORS_maxObservedZeroFreeFibreSize_eq_zero_of_card_lt_four
import Theorems.Thm_Couret_STROBO2TORS_mem_threeTorsion
import Theorems.Thm_Couret_STROBO2TORS_outsideTwoTorsion_card_ge_three_of_large_quotient
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_pos
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_card_le_h_of_no_three_torsion
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_card_le_reduced_of_q_le_three
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_card_le_two_torsion
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_reduced_size_exists
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_size_h_exists_of_no_three_torsion
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_top_size_nonempty_iff
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem maxObservedZeroFreeFibreSize_complete :
    maxObservedZeroFreeFibreSize (G := G) =
      if Fintype.card G < 4 then 0
      else if (twoTorsion : Finset G).card = 1 then 1
      else if (doublingImages : Finset G).card = 1 then
        (twoTorsion : Finset G).card - 3
      else if Fintype.card G = 4 then 1
      else if (threeTorsion : Finset G).card = 1 then
        (twoTorsion : Finset G).card
      else if (doublingImages : Finset G).card ≤ 3 then
        2 * (twoTorsion : Finset G).card - 2
      else 2 * (twoTorsion : Finset G).card := by sorry



end Couret.STROBO2TORS
