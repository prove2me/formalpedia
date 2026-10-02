-- Prove2me | Theorems.Thm_Arexychen_Erdos180_matchingConstruction_extremalFamily_eventually_half_le
-- name    : Arexychen.Erdos180.matchingConstruction_extremalFamily_eventually_half_le
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T07:19:34.985982+00:00
-- url     : https://prove2.me/theorems/65a60f6d-a588-438c-b070-0b74c970e376
-- title:
--   A matching construction gives an eventual $\lfloor n/2\rfloor$ lower bound
-- statement:
--   Let $F$ be a family of finite simple graphs indexed by a finite nonempty type. Assume every member has at least two edges after deleting isolated vertices, and no reduced member has at most one neighbor per vertex. Then, for all sufficiently large natural $n$,
--
--   $$\lfloor n/2\rfloor\le\operatorname{ex}_F(n).$$
--
--   The two-edge hypothesis is retained as a binder even though the source proof does not use it.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/Families/Matching.lean#L146-L166

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

theorem Arexychen.Erdos180.matchingConstruction_extremalFamily_eventually_half_le
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (_hTwo : ∀ i : ι, (F i).atLeastTwoEdgesAfterDeletingIsolated)
    (hNoMatching : ∀ i : ι, ¬ (F i).matchingAfterDeletingIsolated) :
    ∀ᶠ n in atTop, n / 2 ≤ extremalFamily F n := by sorry
