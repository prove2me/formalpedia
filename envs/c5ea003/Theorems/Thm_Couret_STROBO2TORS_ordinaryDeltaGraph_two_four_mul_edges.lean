-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_ordinaryDeltaGraph_two_four_mul_edges
-- name    : Couret.STROBO2TORS.ordinaryDeltaGraph_two_four_mul_edges
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:26:00.020205+00:00
-- url     : https://prove2.me/theorems/78c1543d-8525-4581-907f-d2f6d44dc9da
-- title:
--   Four times the number of ordinary difference-two edges
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. Let $e_2$ be the number of unordered edges joining distinct triples related by a two-torsion translation with symmetric difference of size two. Then
--
--   $$4e_2=N(N-2)(h-1).$$
--
--   This retains exact natural-number counting without dividing.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaTwoCount.lean, lines 356–364; source file SHA-256 cb89a555428b446017e32cc8ccac7e557459a109f1144b64f2304523abb8127d; theorem Couret.STROBO2TORS.ordinaryDeltaGraph_two_four_mul_edges

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
import Theorems.Thm_Couret_STROBO2TORS_deltaTwoOrderedPairs_card_eq_twice_edges
import Theorems.Thm_Couret_STROBO2TORS_twice_deltaTwoOrderedPairs_card
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

theorem ordinaryDeltaGraph_two_four_mul_edges :
    4 * (ordinaryDeltaGraph (G := G) 2).edgeFinset.card =
      Fintype.card G * (Fintype.card G - 2) *
        ((twoTorsion : Finset G).card - 1) := by sorry



end Couret.STROBO2TORS
