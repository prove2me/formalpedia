-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_edge_bound__p2m_a676df72_8370_487d_8148_6fb0674d69c1_a2
-- name    : WilliamsonShmoys.planar_completion_edge_bound__p2m_a676df72_8370_487d_8148_6fb0674d69c1_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:59:15.12422+00:00
-- url     : https://prove2.me/theorems/b0145246-d8dd-48d5-8802-84175e2e6dd9
-- title:
--   Every drawable graph has a completion meeting the planar edge lower bound
-- statement:
--   Every finite graph with a crossing-free drawing on at least three vertices is contained in a crossing-free supergraph on the same vertex set with at least 3|V| - 6 edges. The parent applies maximality to identify that supergraph with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_edge_bound__p2m_a676df72_8370_487d_8148_6fb0674d69c1_a2 {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 <= Fintype.card V) :
    Exists fun N : SimpleGraph V => M <= N /\ HasPlanarDrawingOn N /\
      3 * Fintype.card V <= N.edgeSet.ncard + 6 := by sorry
