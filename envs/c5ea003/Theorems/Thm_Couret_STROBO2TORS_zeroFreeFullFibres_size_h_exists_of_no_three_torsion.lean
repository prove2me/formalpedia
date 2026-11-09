-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_size_h_exists_of_no_three_torsion
-- name    : Couret.STROBO2TORS.zeroFreeFullFibres_size_h_exists_of_no_three_torsion
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:39:19.922832+00:00
-- url     : https://prove2.me/theorems/e3932e49-0708-4e83-8be2-a1dc810a0a59
-- title:
--   A full-size ordinary zero-free fibre exists outside two-torsion
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. If $t=1$ and $|G\setminus H|\ge3$, then
--
--   $$\exists R\in\mathcal F^*,\quad|R|=h.$$
--
--   Thus the ordinary upper bound is attained under these hypotheses.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsSharpMaximum.lean, lines 184–236; source file SHA-256 98c3b135eb2ea85402b9696299566a40098ac965175f8307832d30ec1e652733; theorem Couret.STROBO2TORS.zeroFreeFullFibres_size_h_exists_of_no_three_torsion

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
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_pos
import Theorems.Thm_Couret_STROBO2TORS_withoutZero_squareFibre
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeSquareFibre_card_of_no_exception
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem zeroFreeFullFibres_size_h_exists_of_no_three_torsion
    (ht : (threeTorsion : Finset G).card = 1)
    (hOutside : 3 ≤
      ((Finset.univ : Finset G) \ (twoTorsion : Finset G)).card) :
    ∃ R : Finset (Finset G),
      R ∈ (zeroFreeFullFibres : Finset (Finset (Finset G))) ∧
      R.card = (twoTorsion : Finset G).card := by sorry





















end Couret.STROBO2TORS
