-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_maxObservedZeroFreeFibreSize_eq_h_sub_three_of_q_one
-- name    : Couret.STROBO2TORS.maxObservedZeroFreeFibreSize_eq_h_sub_three_of_q_one
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:39:18.022649+00:00
-- url     : https://prove2.me/theorems/5431b634-1398-4366-93eb-0d9f3ea82b2e
-- title:
--   Maximum zero-free fibre size for trivial doubling image
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. Assume the image of the doubling map has cardinality one and $n\ge4$. Then the defined maximum observed zero-free fibre size is $$M(G)=h-3.$$
--
--   This concerns the maximum over the observed nonempty zero-free fibre family.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsSharpMaximum.lean, lines 253–315; source file SHA-256 98c3b135eb2ea85402b9696299566a40098ac965175f8307832d30ec1e652733; theorem Couret.STROBO2TORS.maxObservedZeroFreeFibreSize_eq_h_sub_three_of_q_one

import Aesop
import Definitions.Def_Couret_Strobo2TorsSharpMaximum_bfb30eac9be9
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_group_card_eq_h_mul_doublingImages
import Theorems.Thm_Couret_STROBO2TORS_maxObservedZeroFreeFibreSize_pos_of_four
import Theorems.Thm_Couret_STROBO2TORS_mem_threeTorsion
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibres_zeroFree_size
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_eq_empty_of_no_three_torsion
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_eq_union
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem maxObservedZeroFreeFibreSize_eq_h_sub_three_of_q_one
    (hq : (doublingImages : Finset G).card = 1)
    (hn : 4 ≤ Fintype.card G) :
    maxObservedZeroFreeFibreSize (G := G) =
      (twoTorsion : Finset G).card - 3 := by sorry















end Couret.STROBO2TORS
