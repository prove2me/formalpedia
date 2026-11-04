-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_e3fcbf10_6f41_4741_b7a4_cf721019c4f7_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_e3fcbf10_6f41_4741_b7a4_cf721019c4f7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:06:33.808188+00:00
-- url     : https://prove2.me/theorems/dcc51884-0da8-465d-ba77-04c61fbeb5d3
-- title:
--   Extend a finite planar drawing to a triangulation
-- statement:
--   Every graph on at least three vertices with a drawing satisfying HasPlanarDrawingOn can be extended on the same vertex type to a drawable graph with exactly 3|V|−6 edges. This is the triangulation-extension step; the parent uses its edge count to contradict the given strict upper bound if the extension were equal to the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_e3fcbf10_6f41_4741_b7a4_cf721019c4f7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hT : HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V,
      T ≤ U ∧ HasPlanarDrawingOn U ∧
        (letI : DecidableRel U.Adj := Classical.decRel U.Adj
         U.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
