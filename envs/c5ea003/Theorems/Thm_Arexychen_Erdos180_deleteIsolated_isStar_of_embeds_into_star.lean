-- Prove2me | Theorems.Thm_Arexychen_Erdos180_deleteIsolated_isStar_of_embeds_into_star
-- name    : Arexychen.Erdos180.deleteIsolated_isStar_of_embeds_into_star
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T07:20:06.808399+00:00
-- url     : https://prove2.me/theorems/48b33985-75ac-42f7-9277-3b5382103b67
-- title:
--   A nonempty subgraph of a star becomes a star after deleting isolates
-- statement:
--   Let $H$ be a simple graph, and suppose there is an injective edge-preserving map from $H$ into the star on a vertex type $\beta$ with center $c\in\beta$. If $H$ has an edge, its induced graph on non-isolated vertices is exactly a star with some center. Neither vertex type is assumed finite.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/Families/Star.lean#L45-L111

import Definitions.Def_arexychen_erdos180_core
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

theorem Arexychen.Erdos180.deleteIsolated_isStar_of_embeds_into_star
    {α : Type u} {β : Type v}
    {H : SimpleGraph α} {c : β}
    (hemb : EmbedsAsSubgraph H (starGraph c))
    (hne : ∃ x y : α, H.Adj x y) :
    IsStar (deleteIsolated H) := by sorry
