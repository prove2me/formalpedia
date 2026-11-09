-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeOrdinaryFibres_card_of_four
-- name    : Couret.STROBO2TORS.zeroFreeOrdinaryFibres_card_of_four
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:58:15.435852+00:00
-- url     : https://prove2.me/theorems/423f7631-951c-47b1-b641-4a80fa48e58c
-- title:
--   Ordinary fibres all survive when two-torsion has size at least four
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. If $h\ge4$, $$|\mathcal O^\circ|=|\mathcal O|.$$
--
--   This compares deduplicated families after deleting zero-containing supports.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsSurvivalCounts.lean, lines 28–46; source file SHA-256 eb83aad035d165b4936c91ba5553308053fd7af14d21de79283c272887a1f571; theorem Couret.STROBO2TORS.zeroFreeOrdinaryFibres_card_of_four

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_nonemptyFullFibres_eq_union
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibres_nonempty_of_four
import Theorems.Thm_Couret_STROBO2TORS_withoutZero_injective_on_nonemptyFullFibres
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

theorem zeroFreeOrdinaryFibres_card_of_four
    (hh : 4 ≤ (twoTorsion : Finset G).card) :
    (zeroFreeOrdinaryFibres : Finset (Finset (Finset G))).card =
      (ordinaryFibres : Finset (Finset (Finset G))).card := by sorry












end Finite
end Couret.STROBO2TORS
