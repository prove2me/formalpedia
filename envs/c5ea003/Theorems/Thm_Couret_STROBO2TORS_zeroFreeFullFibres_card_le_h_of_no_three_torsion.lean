-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_card_le_h_of_no_three_torsion
-- name    : Couret.STROBO2TORS.zeroFreeFullFibres_card_le_h_of_no_three_torsion
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:39:40.765084+00:00
-- url     : https://prove2.me/theorems/06777432-136d-48ef-9383-552e76bf2409
-- title:
--   No three-torsion bounds each zero-free fibre by two-torsion
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. Assume $t=1$. Every observed zero-free full fibre $F\in\mathcal F^\circ$ satisfies $$|F|\le h.$$
--
--   The condition means there is no nonzero three-torsion.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsMaximumCases.lean, lines 24–35; source file SHA-256 1bfee4188b3c47a03a161a1e69038d93494311971f5cf01ae94bd27298727282; theorem Couret.STROBO2TORS.zeroFreeFullFibres_card_le_h_of_no_three_torsion

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_eq_empty_of_no_three_torsion
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_eq_union
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeOrdinaryFibres_card_le_twoTorsion
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]

theorem zeroFreeFullFibres_card_le_h_of_no_three_torsion
    (ht : (threeTorsion : Finset G).card = 1)
    (F : Finset (Finset G))
    (hF : F ∈ (zeroFreeFullFibres : Finset (Finset (Finset G)))) :
    F.card ≤ (twoTorsion : Finset G).card := by sorry

























end Finite
end Couret.STROBO2TORS
