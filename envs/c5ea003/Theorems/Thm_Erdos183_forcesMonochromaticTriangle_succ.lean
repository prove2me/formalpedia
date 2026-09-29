-- Prove2me | Theorems.Thm_Erdos183_forcesMonochromaticTriangle_succ
-- name    : Erdos183.forcesMonochromaticTriangle_succ
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T00:15:44.208027+00:00
-- url     : https://prove2.me/theorems/122aadda-9891-412f-993e-458855bbd004
-- title:
--   Recursive step for forcing a monochromatic triangle
-- statement:
--   If $n$ forces a monochromatic triangle for $k$ colours, then $1 + (k+1)n$ forces one for $k+1$ colours:
--
--   $$n \to k \quad\Longrightarrow\quad 1 + (k+1)\,n \to k+1.$$
--
--   This is the classical pigeonhole recursion. Fix a vertex $v$ in a complete graph on $1 + (k+1)n$ vertices; its $(k+1)n$ incident edges receive $k+1$ colours, so some colour class contains at least $n$ of the neighbours. Either two of those neighbours are joined by an edge of that same colour, giving a monochromatic triangle through $v$, or that colour is absent among them and the inductive hypothesis applies to the remaining $k$ colours on those $n$ vertices.
-- source:
--   OpenAI, Ten Advances in Mathematics and Theoretical Computer Science, https://cdn.openai.com/pdf/ten-proofs-oai.pdf; Lean source https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L241-L310

import Definitions.Def_erdos183_core
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling

open Filter Finset SimpleGraph
open scoped Topology
open Erdos183

theorem Erdos183.forcesMonochromaticTriangle_succ {n k : ℕ}
    (hn : ForcesMonochromaticTriangle n k) :
    ForcesMonochromaticTriangle (1 + (k + 1) * n) (k + 1) := by sorry
