-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_all_reduced_of_q_le_three
-- name    : Couret.STROBO2TORS.zeroFreeExceptionalFibres_all_reduced_of_q_le_three
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:26:08.77062+00:00
-- url     : https://prove2.me/theorems/46e3c558-2d09-4e64-aebd-5fb48cdd3982
-- title:
--   All zero-free exceptional fibres are reduced when the doubling image is small
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. If $q\le3$, then every zero-free image $R=F^\circ$ of an exceptional fibre satisfies
--
--   $$|R|=2h-2.$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsZeroFree.lean, lines 462–474; source file SHA-256 5b8447d710c8e734bf9ff71c397ece8eebe34e569041c803c65dea8a9c580a24; theorem Couret.STROBO2TORS.zeroFreeExceptionalFibres_all_reduced_of_q_le_three

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_zeroFree_card
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_full_nonempty_iff
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



section Finite

variable [Fintype G]

theorem zeroFreeExceptionalFibres_all_reduced_of_q_le_three
    (hq : (doublingImages : Finset G).card ≤ 3) (F : Finset (Finset G))
    (hF : F ∈ (zeroFreeExceptionalFibres : Finset (Finset (Finset G)))) :
    F.card = 2 * (twoTorsion : Finset G).card - 2 := by sorry


end Finite
end Couret.STROBO2TORS
