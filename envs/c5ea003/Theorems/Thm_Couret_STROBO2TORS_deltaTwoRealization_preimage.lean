-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_deltaTwoRealization_preimage
-- name    : Couret.STROBO2TORS.deltaTwoRealization_preimage
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:01:13.805034+00:00
-- url     : https://prove2.me/theorems/128da722-5fe4-417d-bf62-4b3dfe7840d8
-- title:
--   Each delta-two ordered pair has two parameters
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. For an ordered ordinary triple pair $(S,T)$ with $|S\cap T|=2$, consider parameters $(a,u,b)$ with $u\in H\setminus\{0\}$ and $b\notin\{a,a+u\}$ realizing $S=\{a,a+u,b\}$ and $T=\{a,a+u,b+u\}$. Then
--
--   $$\#\{(a,u,b)\text{ realizing }(S,T)\}=2.$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaTwoCount.lean, lines 239–306; source file SHA-256 cb89a555428b446017e32cc8ccac7e557459a109f1144b64f2304523abb8127d; theorem Couret.STROBO2TORS.deltaTwoRealization_preimage

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
import Theorems.Thm_Couret_STROBO2TORS_deltaTwoRealization_image
import Theorems.Thm_Couret_STROBO2TORS_translateSupport_injective_on_two_torsion
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

theorem deltaTwoRealization_preimage (P : Finset G × Finset G)
    (hP : P ∈ deltaTwoOrderedPairs) :
    ((deltaTwoParameters : Finset (DeltaTwoParameter G)).filter
      (fun p => deltaTwoRealization p = P)).card = 2 := by sorry











end Couret.STROBO2TORS
