-- Prove2me | Theorems.Thm_Erdos180_edgeFinset_card_eq_natCard
-- name    : Erdos180.edgeFinset_card_eq_natCard
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T01:58:12.639583+00:00
-- url     : https://prove2.me/theorems/83283864-f8a0-4644-9f19-1d815ef36012
-- title:
--   Edge count as a cardinal
-- statement:
--   For a simple graph $G$ with finite edge set, the cardinality of its edge finset agrees
--   with $\mathrm{Nat.card}$ of its edge set:
--
--   $$|E(G)| \;=\; \#\, E(G).$$
--
--   A bookkeeping identity that lets the edge counts of §3 and §4 of the source be manipulated
--   interchangeably in either form.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L50-L54

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.SetTheory.Cardinal.Finite

open Erdos180
open Finset SimpleGraph
open scoped Classical

theorem Erdos180.edgeFinset_card_eq_natCard {V : Type*} (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    G.edgeFinset.card = Nat.card G.edgeSet := by sorry
