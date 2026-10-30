-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_f3b09488_81b3_4c0a_8ec2_c4e84638c6d1_a15
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_f3b09488_81b3_4c0a_8ec2_c4e84638c6d1_a15
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:13:32.324529+00:00
-- url     : https://prove2.me/theorems/17a75713-fb5d-4021-b2ef-65b0ce368155
-- title:
--   Maximal drawable graphs have at least 3n−6 edges
-- statement:
--   A drawable graph that is inclusion-maximal among drawable supergraphs on the same vertex type, with at least three vertices, has at least 3|V|−6 edges. This supplies the lower half of the parent equality. The proof route is to use maximality to establish connectedness and that faces are triangles (or obtain an equivalent incidence bound), then count face-edge incidences with Euler’s formula. It must handle the three-vertex boundary and disconnected starting graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Card

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_f3b09488_81b3_4c0a_8ec2_c4e84638c6d1_a15
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hMax : And (WilliamsonShmoys.HasPlanarDrawingOn H)
      (forall J : SimpleGraph V, H <= J ->
        WilliamsonShmoys.HasPlanarDrawingOn J -> J <= H))
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V - 6 <= H.edgeSet.ncard := by
  sorry
