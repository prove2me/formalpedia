-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_threeTorsion_nonzero_card_eq_two_pairs
-- name    : Couret.STROBO2TORS.threeTorsion_nonzero_card_eq_two_pairs
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:48:32.665178+00:00
-- url     : https://prove2.me/theorems/794552f5-f9e3-4ee7-a2ec-38d4b0a6d9e5
-- title:
--   Nonzero three-torsion splits into sign pairs
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. Let $\mathcal S=\{\{v,-v\}:v\in K\setminus\{0\}\}$. Then
--
--   $$t-1=2|\mathcal S|.$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsEnumeration.lean, lines 410–425; source file SHA-256 c5994a3923540d425df056cc4b93ff327cc2020eebfa6a424ceca158f26761bc; theorem Couret.STROBO2TORS.threeTorsion_nonzero_card_eq_two_pairs

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_threeTorsion
import Theorems.Thm_Couret_STROBO2TORS_threeSignPairs_preimage
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]

theorem threeTorsion_nonzero_card_eq_two_pairs :
    (threeTorsion : Finset G).card - 1 = 2 * (threeSignPairs : Finset (Finset G)).card := by sorry
































end Finite
end Couret.STROBO2TORS
