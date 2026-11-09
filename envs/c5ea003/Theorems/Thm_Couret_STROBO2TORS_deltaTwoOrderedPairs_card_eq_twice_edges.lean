-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_deltaTwoOrderedPairs_card_eq_twice_edges
-- name    : Couret.STROBO2TORS.deltaTwoOrderedPairs_card_eq_twice_edges
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:16:21.958366+00:00
-- url     : https://prove2.me/theorems/d18755d5-4ecd-45bf-9680-4b254a225e49
-- title:
--   Ordered pairs count each distance-two edge twice
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. Let $P_2$ be the defined ordered-pair family and $\Gamma^{\mathrm{ord}}_2$ the ordinary collision graph with symmetric-difference size two. Then $$|P_2|=2|E(\Gamma^{\mathrm{ord}}_2)|.$$ Each edge is counted in both directions.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaTwoCount.lean, lines 341–354; source file SHA-256 cb89a555428b446017e32cc8ccac7e557459a109f1144b64f2304523abb8127d; theorem Couret.STROBO2TORS.deltaTwoOrderedPairs_card_eq_twice_edges

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
import Theorems.Thm_Couret_STROBO2TORS_deltaTwoOrderedPairs_iff_adj
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

theorem deltaTwoOrderedPairs_card_eq_twice_edges :
    (deltaTwoOrderedPairs : Finset (Finset G × Finset G)).card =
      2 * (ordinaryDeltaGraph (G := G) 2).edgeFinset.card := by sorry





end Couret.STROBO2TORS
