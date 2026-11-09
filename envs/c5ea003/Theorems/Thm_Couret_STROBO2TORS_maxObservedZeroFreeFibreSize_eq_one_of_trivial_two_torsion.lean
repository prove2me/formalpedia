-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_maxObservedZeroFreeFibreSize_eq_one_of_trivial_two_torsion
-- name    : Couret.STROBO2TORS.maxObservedZeroFreeFibreSize_eq_one_of_trivial_two_torsion
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:39:25.43393+00:00
-- url     : https://prove2.me/theorems/66cac031-258a-470b-a20e-eac3766996bc
-- title:
--   Trivial two-torsion makes the largest observed zero-free fibre a singleton
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. If $h=1$ and $N\ge4$, the maximum size $M$ of a nonempty zero-free triple square fibre is
--
--   $$M=1.$$
--
--   The cardinality lower bound ensures at least one zero-free triple exists.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsSharpMaximum.lean, lines 158–181; source file SHA-256 98c3b135eb2ea85402b9696299566a40098ac965175f8307832d30ec1e652733; theorem Couret.STROBO2TORS.maxObservedZeroFreeFibreSize_eq_one_of_trivial_two_torsion

import Aesop
import Definitions.Def_Couret_Strobo2TorsSharpMaximum_bfb30eac9be9
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_card_numeric
import Theorems.Thm_Couret_STROBO2TORS_maxObservedZeroFreeFibreSize_pos_of_four
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_eq_union
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeOrdinaryFibres_card_le_twoTorsion
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem maxObservedZeroFreeFibreSize_eq_one_of_trivial_two_torsion
    (hh : (twoTorsion : Finset G).card = 1)
    (hn : 4 ≤ Fintype.card G) :
    maxObservedZeroFreeFibreSize (G := G) = 1 := by sorry
























end Couret.STROBO2TORS
