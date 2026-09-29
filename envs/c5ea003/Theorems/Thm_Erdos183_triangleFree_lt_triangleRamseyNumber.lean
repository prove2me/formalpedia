-- Prove2me | Theorems.Thm_Erdos183_triangleFree_lt_triangleRamseyNumber
-- name    : Erdos183.triangleFree_lt_triangleRamseyNumber
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T00:16:30.37257+00:00
-- url     : https://prove2.me/theorems/a09fca97-e27c-4947-82a5-979bbf27a752
-- title:
--   A triangle-free colouring bounds the Ramsey number from below
-- statement:
--   If there exists a triangle-free $k$-colouring of the edges of $K_n$, then $n < R_k$.
--
--   Here $R_k$ denotes the $k$-colour triangle Ramsey number `triangleRamseyNumber k`: the least $n$ such that every colouring of the edges of the complete graph $K_n$ with $k$ colours contains a monochromatic triangle. This is the bridge from construction to bound: every explicit triangle-free colouring produced by the palette recursion immediately certifies a lower bound on the Ramsey number.
-- source:
--   OpenAI, Ten Advances in Mathematics and Theoretical Computer Science, https://cdn.openai.com/pdf/ten-proofs-oai.pdf; Lean source https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L364-L373

import Definitions.Def_erdos183_core
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling

open Filter Finset SimpleGraph
open scoped Topology
open Erdos183

theorem Erdos183.triangleFree_lt_triangleRamseyNumber {n k : ℕ}
    (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k))
    (hC : TriangleFree C) :
    n < triangleRamseyNumber k := by sorry
