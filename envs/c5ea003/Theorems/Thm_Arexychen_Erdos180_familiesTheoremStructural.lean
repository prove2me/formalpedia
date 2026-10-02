-- Prove2me | Theorems.Thm_Arexychen_Erdos180_familiesTheoremStructural
-- name    : Arexychen.Erdos180.familiesTheoremStructural
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T07:20:31.567933+00:00
-- url     : https://prove2.me/theorems/29d7dc04-f4bc-44b3-af44-0c601a63a17e
-- title:
--   Structural constant-or-linear dichotomy for finite forest families
-- statement:
--   Let $F$ be a family of finite simple graphs indexed by a finite nonempty type. Suppose every reduced member, obtained by deleting isolated vertices, is acyclic and has at least two edges. Then exactly the following stated alternatives are classified:
--
--   $$\bigl(P(F)\land\operatorname{ex}_F(n)=\Theta(1)\bigr)\;\lor\;\bigl(\neg P(F)\land\operatorname{ex}_F(n)=\Theta(n)\bigr),$$
--
--   where $P(F)$ means that the family contains a reduced star with at least two edges and a reduced matching with at least two edges. The asymptotic comparisons are as natural $n\to\infty$, with real casts. The extremal function forbids ordinary subgraph copies of the original members, including isolated vertices. This is a formalization of the forest/linear regime related to Erdős Problem #180, with no claim of mathematical novelty.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/Families/StructuralTheorem.lean#L79-L94

import Definitions.Def_arexychen_erdos180_core
import Definitions.Def_arexychen_erdos180_families_bounds
import Definitions.Def_arexychen_erdos180_finite
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Tactic

open Filter
open Asymptotics
universe u v w
open Arexychen.Erdos180

theorem Arexychen.Erdos180.familiesTheoremStructural
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (hforest : ∀ i : ι, ((F i).reduced).IsAcyclic)
    (htwo : ∀ i : ι, (F i).atLeastTwoEdgesAfterDeletingIsolated) :
    (FamilyContainsStarMatchingPair F ∧
        IsThetaConstant (fun n : ℕ => extremalFamily F n)) ∨
      (¬ FamilyContainsStarMatchingPair F ∧
        IsThetaLinear (fun n : ℕ => extremalFamily F n)) := by sorry
