-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_twice_deltaTwoOrderedPairs_card
-- name    : Couret.STROBO2TORS.twice_deltaTwoOrderedPairs_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:16:46.711563+00:00
-- url     : https://prove2.me/theorems/a26ce902-6172-4803-8a74-ca42c32395f4
-- title:
--   Weighted count of ordinary delta-two ordered pairs
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. Let $\mathcal P_2$ be ordered pairs of triples related by a two-torsion translation and having intersection size two. Then
--
--   $$2|\mathcal P_2|=n(n-2)(h-1).$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaTwoCount.lean, lines 308–324; source file SHA-256 cb89a555428b446017e32cc8ccac7e557459a109f1144b64f2304523abb8127d; theorem Couret.STROBO2TORS.twice_deltaTwoOrderedPairs_card

import Aesop
import Definitions.Def_Couret_Strobo2TorsDeltaTwoCount_96c8f007ba6a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_deltaTwoParameters_card
import Theorems.Thm_Couret_STROBO2TORS_deltaTwoRealization_image
import Theorems.Thm_Couret_STROBO2TORS_deltaTwoRealization_preimage
import Definitions.Def_Couret_Strobo2TorsDeltaOrdinaryCount_91279c99d3e0

set_option autoImplicit false

open scoped BigOperators symmDiff

/-!
Exact count of the ordinary delta-two edges, with zero allowed.

Parameters (a,u,b) have u a nonzero element of G[2] and b outside
{a,a+u}. They represent the ordered pair
({a,a+u,b}, {a,a+u,b+u}). Each ordered pair has precisely two
parameters, according to the choice a or a+u in its common pair.
The graph handshake supplies the second factor of two.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]













variable [Fintype G]











attribute [local instance] Classical.propDecidable

theorem twice_deltaTwoOrderedPairs_card :
    2 * (deltaTwoOrderedPairs : Finset (Finset G × Finset G)).card =
      Fintype.card G * (Fintype.card G - 2) *
        ((twoTorsion : Finset G).card - 1) := by sorry









end Couret.STROBO2TORS
