-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_bc55d69b_5743_4927_884d_0327a4a2fa7c_a1
-- name    : WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_bc55d69b_5743_4927_884d_0327a4a2fa7c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:55:24.906374+00:00
-- url     : https://prove2.me/theorems/155e3131-f4ce-4fb5-b73d-ce5928aca9fe
-- title:
--   Drawable graph extension with maximal planar edge count
-- statement:
--   Every drawable finite simple graph with at least three vertices can be extended, on the same vertex set and while retaining all its edges, to a drawable graph with exactly 3|V|−6 edges. This isolates the topological work: extend the drawing to a triangulation and count its edges using Euler’s formula and face-edge incidences. The condition |V| ≥ 3 is needed for the stated edge count, including the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_bc55d69b_5743_4927_884d_0327a4a2fa7c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V - 6 = N.edgeSet.ncard := by sorry
