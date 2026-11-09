-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_card_le_reduced_of_q_le_three
-- name    : Couret.STROBO2TORS.zeroFreeFullFibres_card_le_reduced_of_q_le_three
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:39:37.420275+00:00
-- url     : https://prove2.me/theorems/d0b1619d-aad1-4572-9341-2ac3708fbdff
-- title:
--   Upper bound for observed fibres with a small doubling image
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. Suppose $q\le3$ and $h\ge2$. Every observed nonempty zero-free full fibre $R$ satisfies
--
--   $$|R|\le2h-2.$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsMaximumCases.lean, lines 37–50; source file SHA-256 1bfee4188b3c47a03a161a1e69038d93494311971f5cf01ae94bd27298727282; theorem Couret.STROBO2TORS.zeroFreeFullFibres_card_le_reduced_of_q_le_three

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_all_reduced_of_q_le_three
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_eq_union
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeOrdinaryFibres_card_le_twoTorsion
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]

theorem zeroFreeFullFibres_card_le_reduced_of_q_le_three
    (hq : (doublingImages : Finset G).card ≤ 3)
    (hh : 2 ≤ (twoTorsion : Finset G).card)
    (F : Finset (Finset G))
    (hF : F ∈ (zeroFreeFullFibres : Finset (Finset (Finset G)))) :
    F.card ≤ 2 * (twoTorsion : Finset G).card - 2 := by sorry























end Finite
end Couret.STROBO2TORS
