-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_nontranslationGraph_twice_edges
-- name    : Couret.STROBO2TORS.nontranslationGraph_twice_edges
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:39:03.83236+00:00
-- url     : https://prove2.me/theorems/6e6ad087-62e7-4f7d-be3c-bd52107a50a8
-- title:
--   Nontranslation edges from exceptional supports
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. For the full nontranslation collision graph $\Gamma^{\mathrm{nt}}$, $$2|E(\Gamma^{\mathrm{nt}})|=|\mathcal S_{\mathrm{exc}}|h.$$
--
--   The factor two converts ordered adjacency into edges.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsNontranslationUnordered.lean, lines 45–77; source file SHA-256 9658a84461c5a4d77889dd76eb3dddcec15835d7b88366ad8625c7d4f9683325; theorem Couret.STROBO2TORS.nontranslationGraph_twice_edges

import Aesop
import Definitions.Def_Couret_Strobo2TorsNontranslationUnordered_7692bff20374
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_directed_nontranslation_degree_sum
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
import Theorems.Thm_Couret_STROBO2TORS_nontranslationGraph_degree
import Definitions.Def_Couret_Strobo2TorsNontranslationSymmetry_29c4a2e9c2a5
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem nontranslationGraph_twice_edges :
    2 * (nontranslationGraph (G := G)).edgeFinset.card =
      (exceptionalSupports : Finset (Finset G)).card *
        (twoTorsion : Finset G).card := by sorry




end Couret.STROBO2TORS
