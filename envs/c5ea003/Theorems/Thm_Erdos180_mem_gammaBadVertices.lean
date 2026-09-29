-- Prove2me | Theorems.Thm_Erdos180_mem_gammaBadVertices
-- name    : Erdos180.mem_gammaBadVertices
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:12:35.458536+00:00
-- url     : https://prove2.me/theorems/c6a238c6-07e4-469f-9d7d-2207caf6c190
-- title:
--   Membership in the bad-vertex set $U$
-- statement:
--   A vertex lies in $U$ exactly when it is *not* a centre of any copy of $S_3$:
--
--   $$v \in U \iff \lnot\,\mathrm{GammaGood}(G, v).$$
--
--   $U$ is the set introduced in the proof of Proposition 3.4 of the source. The argument bounds
--   $|U|$ from above and then shows $U$ is a vertex cover, which forces the edge count down.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L5444-L5448

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Basic

open Erdos180
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem Erdos180.mem_gammaBadVertices (G : SimpleGraph V) (v : V) :
    v ∈ gammaBadVertices G ↔ ¬ GammaGood G v := by sorry
