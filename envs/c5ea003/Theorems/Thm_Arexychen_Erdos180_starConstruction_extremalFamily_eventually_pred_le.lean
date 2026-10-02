-- Prove2me | Theorems.Thm_Arexychen_Erdos180_starConstruction_extremalFamily_eventually_pred_le
-- name    : Arexychen.Erdos180.starConstruction_extremalFamily_eventually_pred_le
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T07:20:26.704521+00:00
-- url     : https://prove2.me/theorems/88bae123-bdd5-44a8-bd60-0facb3d1ba37
-- title:
--   A star construction gives an eventual $n-1$ lower bound
-- statement:
--   Let $F$ be a family of finite simple graphs indexed by a finite nonempty type. Suppose every member has at least two edges after deleting isolated vertices, and none of the reduced members is a star. Then, for all sufficiently large natural $n$,
--
--   $$n-1\le\operatorname{ex}_F(n).$$
--
--   Subtraction is natural-number subtraction, and freeness concerns the original forbidden graphs.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/Families/Star.lean#L113-L143

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

theorem Arexychen.Erdos180.starConstruction_extremalFamily_eventually_pred_le
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (hTwo : ∀ i : ι, (F i).atLeastTwoEdgesAfterDeletingIsolated)
    (hNoStar : ∀ i : ι, ¬ (F i).starAfterDeletingIsolated) :
    ∀ᶠ n in atTop, n - 1 ≤ extremalFamily F n := by sorry
