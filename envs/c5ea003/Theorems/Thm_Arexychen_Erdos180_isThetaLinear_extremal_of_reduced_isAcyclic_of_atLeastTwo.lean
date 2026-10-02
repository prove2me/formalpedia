-- Prove2me | Theorems.Thm_Arexychen_Erdos180_isThetaLinear_extremal_of_reduced_isAcyclic_of_atLeastTwo
-- name    : Arexychen.Erdos180.isThetaLinear_extremal_of_reduced_isAcyclic_of_atLeastTwo
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T07:19:45.285515+00:00
-- url     : https://prove2.me/theorems/552522d2-72fe-4204-afbb-74b2df845c33
-- title:
--   A reduced forest with at least two edges has linear extremal growth
-- statement:
--   Let $H$ be a finite simple graph whose induced graph on non-isolated vertices is acyclic and has at least two edges. Its extremal function for ordinary subgraph freeness of the original $H$ satisfies
--
--   $$\operatorname{ex}_H(n)=\Theta(n)\qquad(n\to\infty).$$
--
--   The comparison is at the natural-number at-top filter after casting the extremal values and $n$ to real numbers; it gives eventual positive constant upper and lower linear bounds.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/Forest.lean#L491-L506

import Definitions.Def_arexychen_erdos180_core
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
attribute [local instance] SimpleGraph.neighborSetFintype
universe u v
open Arexychen.Erdos180

theorem Arexychen.Erdos180.isThetaLinear_extremal_of_reduced_isAcyclic_of_atLeastTwo
    (H : FiniteSimpleGraph.{u})
    (hforest : H.reduced.IsAcyclic)
    (htwo : H.atLeastTwoEdgesAfterDeletingIsolated) :
    IsThetaLinear (fun n => H.extremal n) := by sorry
