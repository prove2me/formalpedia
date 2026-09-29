-- Prove2me | solution 1 for Erdos146.hammingHost_adj_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:34:30.546088+00:00
-- url     : https://prove2.me/submissions/e3dfaac1-ba15-4889-817e-285e5fc08c53

import Definitions.Def_erdos146_core2
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.InformationTheory.Hamming

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution (dimension radius : ℕ)
    (x y : Bool × HammingWord dimension) :
    (hammingHost dimension radius).Adj x y ↔
      x.1 ≠ y.1 ∧ hammingDist x.2 y.2 ≤ radius := by
  rw [hammingHost, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, hforward | hbackward⟩
    · exact hforward
    · exact ⟨Ne.symm hbackward.1, by
        simpa [hammingDist_comm] using hbackward.2⟩
  · intro hxy
    refine ⟨?_, Or.inl hxy⟩
    intro heq
    exact hxy.1 (congrArg Prod.fst heq)
