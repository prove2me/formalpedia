-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_directed_nontranslation_degree_sum_numeric
-- name    : Couret.STROBO2TORS.directed_nontranslation_degree_sum_numeric
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:38:52.948669+00:00
-- url     : https://prove2.me/theorems/16596ec7-bbc7-4037-ae0d-1c83a9c0ccbf
-- title:
--   Total directed nontranslation degree
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. For each three-element support $S$, let $N(S)$ be its nontranslated square-collision neighbours. Then $$\sum_{|S|=3}|N(S)|=n(h-1)(t-1)h.$$ All subtractions and products are in the natural numbers.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsNontranslationDegree.lean, lines 122–130; source file SHA-256 bb81c661856c1b823aeeb307e2603c5cb0aee20a082885d1c0ea1a2cc7b78ead; theorem Couret.STROBO2TORS.directed_nontranslation_degree_sum_numeric

import Aesop
import Definitions.Def_Couret_Strobo2TorsNontranslationDegree_16ff2822736a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_directed_nontranslation_degree_sum
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupports_card
import Definitions.Def_Couret_Strobo2TorsNontranslationBridge_e18319b1ae30
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem directed_nontranslation_degree_sum_numeric :
    (∑ S ∈ (tripleSupports : Finset (Finset G)),
        (nontranslatedNeighbours S).card) =
      (Fintype.card G * ((twoTorsion : Finset G).card - 1) *
        ((threeTorsion : Finset G).card - 1)) *
        (twoTorsion : Finset G).card := by sorry


end Couret.STROBO2TORS
