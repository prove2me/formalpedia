-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_reduced_size_exists
-- name    : Couret.STROBO2TORS.zeroFreeFullFibres_reduced_size_exists
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:39:15.378853+00:00
-- url     : https://prove2.me/theorems/43e7e559-317c-445a-9837-8be4251412c7
-- title:
--   A reduced observed fibre exists when both torsion groups are nontrivial
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. If $h>1$ and $t>1$, there exists $R$ among the observed nonempty zero-free full fibres with
--
--   $$|R|=2h-2.$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsMaximumCases.lean, lines 52–73; source file SHA-256 1bfee4188b3c47a03a161a1e69038d93494311971f5cf01ae94bd27298727282; theorem Couret.STROBO2TORS.zeroFreeFullFibres_reduced_size_exists

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_threeTorsion_nonzero_card_eq_two_pairs
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_reduced_card
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_eq_union
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]

theorem zeroFreeFullFibres_reduced_size_exists
    (hh : 1 < (twoTorsion : Finset G).card)
    (ht : 1 < (threeTorsion : Finset G).card) :
    ∃ F : Finset (Finset G),
      F ∈ (zeroFreeFullFibres : Finset (Finset (Finset G))) ∧
      F.card = 2 * (twoTorsion : Finset G).card - 2 := by sorry





















end Finite
end Couret.STROBO2TORS
