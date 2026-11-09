-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_nontranslationGraph_degree
-- name    : Couret.STROBO2TORS.nontranslationGraph_degree
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:37.971305+00:00
-- url     : https://prove2.me/theorems/024a0831-d484-4899-94b3-3daa47fe5189
-- title:
--   Degree in the full nontranslation collision graph
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. In the graph joining nontranslation square-colliding triples, for every finite support $S$,
--
--   $$\deg(S)=\begin{cases}|F(S)\setminus O(S)|&|S|=3,\\0&|S|\ne3.\end{cases}$$
--
--   This connects the graph interface with explicit neighbours.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsNontranslationUnordered.lean, lines 29–43; source file SHA-256 9658a84461c5a4d77889dd76eb3dddcec15835d7b88366ad8625c7d4f9683325; theorem Couret.STROBO2TORS.nontranslationGraph_degree

import Aesop
import Definitions.Def_Couret_Strobo2TorsNontranslationUnordered_7692bff20374
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsNontranslationSymmetry_29c4a2e9c2a5
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem nontranslationGraph_degree (S : Finset G) :
    (nontranslationGraph (G := G)).degree S =
      if hS : S.card = 3 then (nontranslatedNeighbours S).card else 0 := by sorry






end Couret.STROBO2TORS
