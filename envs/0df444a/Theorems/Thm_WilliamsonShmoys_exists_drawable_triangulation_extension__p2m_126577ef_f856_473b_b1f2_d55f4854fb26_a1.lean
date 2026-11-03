-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_triangulation_extension__p2m_126577ef_f856_473b_b1f2_d55f4854fb26_a1
-- name    : WilliamsonShmoys.exists_drawable_triangulation_extension__p2m_126577ef_f856_473b_b1f2_d55f4854fb26_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:35:00.936288+00:00
-- url     : https://prove2.me/theorems/b4f778a6-f898-4626-8a06-345c4a75a344
-- title:
--   Extend a drawable graph to a triangulation on the same vertices
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertices with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.exists_drawable_triangulation_extension__p2m_126577ef_f856_473b_b1f2_d55f4854fb26_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        (letI : DecidableRel L.Adj := Classical.decRel L.Adj
         L.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
