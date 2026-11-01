-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_e31b05a7_4e78_4789_8a19_ecdeedbcdfa7_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_e31b05a7_4e78_4789_8a19_ecdeedbcdfa7_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:38:34.506038+00:00
-- url     : https://prove2.me/theorems/2b02d0f4-e4a5-4246-8c79-3e972b456778
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no drawable strict supergraph on the same vertex set has exactly 3|V|−6 edges. This supplies the topological and edge-count result used after finite maximality. The independent proof route is to represent the drawing as a plane embedding, use maximality to show every face is a triangle, and combine 3F=2E with Euler’s formula. The boundary case of three vertices is the triangle. Formalizing this route for the given arc-based drawing predicate is the remaining core mathematical obligation; maximality alone does not prove the edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_e31b05a7_4e78_4789_8a19_ecdeedbcdfa7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    letI : DecidableRel N.Adj := Classical.decRel N.Adj
    N.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
