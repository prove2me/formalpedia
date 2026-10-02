-- Prove2me | Theorems.Thm_Arexychen_Erdos180_oneEdgeConstruction_extremalFamily_eventually_one_le
-- name    : Arexychen.Erdos180.oneEdgeConstruction_extremalFamily_eventually_one_le
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T07:20:03.31101+00:00
-- url     : https://prove2.me/theorems/79f08f94-cf6a-4452-b3bc-04ead398f99e
-- title:
--   A one-edge construction gives an eventual positive family lower bound
-- statement:
--   Let $F$ be a family of finite simple graphs indexed by a finite nonempty type. If every member has at least two edges after deleting isolated vertices, then $1\le\operatorname{ex}_F(n)$ for all sufficiently large natural $n$. Here the family extremal function uses ordinary subgraph freeness of the whole members.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/Families/OneEdge.lean#L90-L111

import Definitions.Def_arexychen_erdos180_families_bounds
import Definitions.Def_arexychen_erdos180_finite
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Tactic

open Filter
open Asymptotics
universe u v w
open Arexychen.Erdos180

theorem Arexychen.Erdos180.oneEdgeConstruction_extremalFamily_eventually_one_le
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (hTwo : ∀ i : ι, (F i).atLeastTwoEdgesAfterDeletingIsolated) :
    ∀ᶠ n in atTop, 1 ≤ extremalFamily F n := by sorry
