-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_d0cbf8fc_b126_4e9b_9c59_f16faa272cb9_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_d0cbf8fc_b126_4e9b_9c59_f16faa272cb9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:32:30.565972+00:00
-- url     : https://prove2.me/theorems/4631bec4-c523-4d65-82d4-b3b590349449
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Every simply drawn planar graph on at least three vertices has at most 3|V|−6 edges. This is the standard Euler upper bound, independent of maximality. A proof route is to obtain a planar embedding from the crossing-free drawing, complete the embedding to count its faces, use Euler’s formula, and use simplicity to bound each face boundary length below by three. The condition |V| ≥ 3 is needed for this bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_d0cbf8fc_b126_4e9b_9c59_f16faa272cb9_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hcard : 3 ≤ Fintype.card V) : letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj; H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
