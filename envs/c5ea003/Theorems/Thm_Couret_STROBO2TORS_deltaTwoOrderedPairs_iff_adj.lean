-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_deltaTwoOrderedPairs_iff_adj
-- name    : Couret.STROBO2TORS.deltaTwoOrderedPairs_iff_adj
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:01:08.045928+00:00
-- url     : https://prove2.me/theorems/7283620e-997b-4da0-8816-ef9168427c78
-- title:
--   Delta-two ordered pairs are ordinary graph arcs
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. For any finite supports $S,T$, membership in the stored family of ordered ordinary triple pairs with $|S\cap T|=2$ is equivalent to adjacency in the ordinary-partner graph restricted to $|S\triangle T|=2$:
--
--   $$(S,T)\in\mathcal P_2\Longleftrightarrow S\sim_{{\rm ord},2}T.$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaTwoCount.lean, lines 326–339; source file SHA-256 cb89a555428b446017e32cc8ccac7e557459a109f1144b64f2304523abb8127d; theorem Couret.STROBO2TORS.deltaTwoOrderedPairs_iff_adj

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
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
import Theorems.Thm_Couret_STROBO2TORS_triple_symmDiff_two_iff_inter_two
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

theorem deltaTwoOrderedPairs_iff_adj (S T : Finset G) :
    (S,T) ∈ deltaTwoOrderedPairs ↔ (ordinaryDeltaGraph (G := G) 2).Adj S T := by sorry







end Couret.STROBO2TORS
