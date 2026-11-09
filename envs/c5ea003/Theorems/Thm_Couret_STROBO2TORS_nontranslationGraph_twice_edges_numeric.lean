-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_nontranslationGraph_twice_edges_numeric
-- name    : Couret.STROBO2TORS.nontranslationGraph_twice_edges_numeric
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:54:37.018375+00:00
-- url     : https://prove2.me/theorems/c111779d-6de7-4401-9485-5c607a1e51a4
-- title:
--   Total number of nontranslation collision edges
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. Let $E^{\rm nt}$ be all unordered pairs of nontranslated triples with equal ordered-square counts. Then
--
--   $$2|E^{\rm nt}|=n(h-1)(t-1)h.$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsNontranslationUnordered.lean, lines 79–86; source file SHA-256 9658a84461c5a4d77889dd76eb3dddcec15835d7b88366ad8625c7d4f9683325; theorem Couret.STROBO2TORS.nontranslationGraph_twice_edges_numeric

import Aesop
import Definitions.Def_Couret_Strobo2TorsNontranslationUnordered_7692bff20374
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupports_card
import Theorems.Thm_Couret_STROBO2TORS_nontranslationGraph_twice_edges
import Definitions.Def_Couret_Strobo2TorsNontranslationSymmetry_29c4a2e9c2a5
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem nontranslationGraph_twice_edges_numeric :
    2 * (nontranslationGraph (G := G)).edgeFinset.card =
      (Fintype.card G * ((twoTorsion : Finset G).card - 1) *
        ((threeTorsion : Finset G).card - 1)) *
        (twoTorsion : Finset G).card := by sorry


end Couret.STROBO2TORS
