-- Prove2me | Theorems.Thm_Erdos180_symplecticQuadrangle_adjacent_to_line
-- name    : Erdos180.symplecticQuadrangle_adjacent_to_line
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:03:27.085008+00:00
-- url     : https://prove2.me/theorems/1885441d-2e3c-472d-96a6-f503d6e10f75
-- title:
--   Neighbours of a line are points on it
-- statement:
--   Every neighbour of a line $L$ in the incidence graph is a point $p$ with $p \le L$.
--
--   The dual of the preceding lemma. Together they say that a connected bipartite subgraph of
--   $I_q$ has each of its own two sides contained in one of $\mathcal{P}$, $\mathcal{M}$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L1212-L1220

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem Erdos180.symplecticQuadrangle_adjacent_to_line
    {L : SymplecticLine K} {v : QuadrangleVertex K}
    (h : (symplecticQuadrangle K).Adj (.inr L) v) :
    ∃ p : SymplecticPoint K, v = .inl p ∧ p.1 ≤ L.1 := by sorry
