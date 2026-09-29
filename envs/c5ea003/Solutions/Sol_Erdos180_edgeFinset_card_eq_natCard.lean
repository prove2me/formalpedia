-- Prove2me | solution 1 for Erdos180.edgeFinset_card_eq_natCard
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:23:10.268715+00:00
-- url     : https://prove2.me/submissions/c1a75705-565e-418b-9521-33c6accf3bb1

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.SetTheory.Cardinal.Finite

open Erdos180
open Finset SimpleGraph
open scoped Classical

theorem solution {V : Type*} (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    G.edgeFinset.card = Nat.card G.edgeSet := by
  simpa only [Nat.card_eq_fintype_card] using
    (SimpleGraph.edgeFinset_card (G := G))
